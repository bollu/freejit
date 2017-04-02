{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}

import qualified LLVM.AST as AST 
import LLVM.AST (Named(..))
import qualified LLVM.AST.Global as G
import qualified LLVM.CodeModel as CodeModel
import qualified LLVM.Module as Module
import LLVM.AST.Constant
import LLVM.AST.Type
import LLVM.AST.Constant (Constant)
import LLVM.AST.AddrSpace
import LLVM.AST.Instruction (Named, Instruction(Mul), Terminator)
import LLVM.AST.Instruction(Instruction(..))
import LLVM.AST.Linkage
import LLVM.AST.Visibility
import LLVM.AST.DLL
import LLVM.AST.CallingConvention as CC
import LLVM.AST.ThreadLocalStorage
import LLVM.AST.Attribute
import LLVM.Target
import LLVM.Context

import Control.Monad.Except
import Data.Int
import Data.Word
import Foreign.Ptr

import LLVM.OrcJIT
import LLVM.OrcJIT.IRCompileLayer (IRCompileLayer, withIRCompileLayer)
import qualified LLVM.OrcJIT.IRCompileLayer as IRCompileLayer
import qualified LLVM.OrcJIT.CompileOnDemandLayer as CODLayer

import Debug.Trace

-- v withModuleInEngine :: e -> Module -> (ExecutableModule e -> IO a) -> IO a
import LLVM.ExecutionEngine
-- v verify
import LLVM.Analysis


foreign import ccall "dynamic"
  mkMain :: FunPtr (IO Int32) -> IO Int32


data Free f a = Leaf a | Roll (f (Free f a))
deriving instance (Show a, Show (f (Free f a))) => Show (Free f a)

instance Functor f => Functor (Free f) where
  fmap f (Leaf a) = Leaf (f a)
  fmap f (Roll f_freefa) = Roll ((fmap . fmap) f f_freefa)

instance (Functor f) => Monad (Free f) where
  return :: a -> Free f a
  return = Leaf

  (>>=) :: Free f a -> (a -> Free f b) -> Free f b
  (>>=) (Leaf a) f = f a
  (>>=) (Roll f_freefa) f = Roll (fmap (>>= f) f_freefa)


instance Functor f => Applicative (Free f) where
  pure = return
  f_atob <*> fa = do
                    a <- fa
                    atob <- f_atob
                    return $ atob a

data Lang next = Create String Int next | Mult String String String next | Return String deriving(Functor)


instance Show next => Show (Lang next) where
  show (Create store val next) = show store ++ " := " ++ show val ++ ";\n" ++ show next
  show (Mult store x y next) = show store ++ " = " ++ show x ++ " * " ++ show y ++ ";\n" ++ show next
  show (Return x) = "Return " ++ show x


liftFree :: Functor f => f a -> Free f a
liftFree stmt = Roll (fmap Leaf stmt) 


mult_ :: String -> String -> String -> Free Lang ()
mult_ store x y = liftFree (Mult store x y ())


(<~) :: String -> Int -> Free Lang ()
(<~) store i = liftFree (Create store i ())

return_ :: String -> Free Lang ()
return_ store = liftFree (Return store)

program :: Free Lang ()
program = do { "x" <~ 10;
               "y" <~ 320;
               "z" <~ 000;
               mult_ "z" "x" "y";
               return_ "z"
          }

prelude :: [Named Instruction]
prelude = [i64Alloc "out"]

i64Alloc :: String -> Named AST.Instruction
i64Alloc rawname = name := alloc where
      name = AST.Name rawname
      alloc = AST.Alloca type_ Nothing alignment metadata
      type_ =  AST.IntegerType 64
      alignment = 8
      metadata = []

varStorei64 :: String -> Int -> Named AST.Instruction
varStorei64 source val = 
    AST.UnName 0 := AST.Store {
      AST.volatile = False,
      AST.address = address,
      AST.value = value,
      AST.maybeAtomicity = Nothing,
      AST.alignment = 8,
      AST.metadata = []
    } where
        address = AST.LocalReference (AST.IntegerType 64) (AST.Name source)
        value = AST.ConstantOperand (Int { integerBits = 64, integerValue = fromIntegral val})

varStoreVar :: String -> String -> Named AST.Instruction
varStoreVar lhs rhs =
    AST.UnName 0 := AST.Store {
      AST.volatile = False,
      AST.address = address,
      AST.value = value,
      AST.maybeAtomicity = Nothing,
      AST.alignment = 8,
      AST.metadata = []
    } where
        address = AST.LocalReference (AST.IntegerType 64) (AST.Name lhs)
        value = AST.LocalReference (AST.IntegerType 64) (AST.Name rhs)


type TempLoadName = String
varLoadi64 :: String -> Named AST.Instruction
varLoadi64 source = AST.Name source := AST.Load {
    AST.volatile = False,
    AST.address = address,
    AST.maybeAtomicity = Nothing,
    AST.alignment = 8,
    AST.metadata = []
  } where
        address = AST.LocalReference (AST.IntegerType 64) (AST.Name source)

code :: Free Lang () -> [Named Instruction]
code (Leaf ()) = []

code (Roll (Create name val next)) = [i64Alloc name, varStorei64 name val] ++ code next
code (Roll (Mult out i j next)) = ([loadi, loadj, mul i j, varStoreVar out "temp"] ++ code next) where
  loadout = varLoadi64 out
  loadi = varLoadi64 i
  loadj = varLoadi64 j
  tempname = "temp"
  mul name1 name2 = AST.Name tempname := AST.Mul {
      AST.nsw = False,
      AST.nuw = False,
      LLVM.AST.Instruction.operand0 = AST.LocalReference (AST.IntegerType 64) (AST.Name i),
      LLVM.AST.Instruction.operand1 = AST.LocalReference (AST.IntegerType 64) (AST.Name j),
      AST.metadata = []
    }


code (Roll (Return store)) = [varLoadi64 store, varStoreVar "out" store, varLoadi64 "out"]

mkBB :: Free Lang () -> G.BasicBlock
mkBB lang = G.BasicBlock (AST.Name "main") (prelude ++ code lang) end where
                end = (AST.Do (AST.Ret {
                          AST.returnOperand = Just (ret),
                          AST.metadata' = []
                      }))
                ret = AST.LocalReference (AST.IntegerType 64) (AST.Name "out")

mkDefinitions :: Free Lang () -> [AST.Definition]
mkDefinitions lang = [AST.GlobalDefinition (G.Function {
                    G.linkage=External,
                    G.visibility=Default,
                    G.dllStorageClass=Nothing,
                    G.callingConvention=CC.C,
                    G.returnAttributes=[],
                    G.functionAttributes=[],
                    G.section= Nothing,
                    G.comdat= Nothing,
                    G.alignment=0,
                    G.garbageCollectorName=Nothing,
                    G.prefix=Nothing,
                    G.personalityFunction=Nothing,
                    -- interesting stuff
                    G.returnType=i64,
                    G.name=AST.Name("main"),
                    G.basicBlocks=[mkBB lang],
                    G.parameters=([], False)
                  })]


mkModule :: [AST.Definition] ->  AST.Module
mkModule defs = AST.Module {
              AST.moduleName="freejit",
              AST.moduleSourceFileName="freejit-thinair",
              AST.moduleDataLayout=Nothing,
              AST.moduleTargetTriple=Nothing,
              AST.moduleDefinitions=defs
          }


withTestModule :: AST.Module -> (Module.Module -> IO a) -> IO (Either String a)
withTestModule mod f = withContext $ \context -> runExceptT (Module.withModuleFromAST context mod f)

resolver :: MangledSymbol -> IRCompileLayer -> MangledSymbol -> IO JITSymbol
resolver testFunc compileLayer symbol
  = IRCompileLayer.findSymbol compileLayer symbol True

nullResolver :: MangledSymbol -> IO JITSymbol
nullResolver s = return (JITSymbol 0 (JITSymbolFlags False False))

failInIO :: ExceptT String IO a -> IO a
failInIO = either fail return <=< runExceptT

eagerJit :: AST.Module -> IO (Either String Int32)
eagerJit amod =
    withTestModule amod $ \mod ->
      failInIO $ withHostTargetMachine $ \tm ->
        withObjectLinkingLayer $ \objectLayer ->
          withIRCompileLayer objectLayer tm $ \compileLayer -> do
            asm <- Module.moduleLLVMAssembly mod
            putStrLn asm
            testFunc <- IRCompileLayer.mangleSymbol compileLayer "main"
            IRCompileLayer.withModuleSet
              compileLayer
              [mod]
              (SymbolResolver (resolver testFunc compileLayer) nullResolver) $
              \moduleSet -> do
                mainSymbol <- IRCompileLayer.mangleSymbol compileLayer "main"
                JITSymbol mainFn _ <- IRCompileLayer.findSymbol compileLayer mainSymbol True
                result <- mkMain (castPtrToFunPtr (wordPtrToPtr mainFn))
                return result


main :: IO ()
main = do
        let mod = mkModule . mkDefinitions $ program
        putStrLn "verifying module..."
        withContext $ \context -> failInIO $ Module.withModuleFromAST context mod (failInIO . verify)
        putStrLn "verified."
 
        llvm_assembly <- (withContext $ \context -> failInIO $ Module.withModuleFromAST context mod Module.moduleLLVMAssembly)

        res <- eagerJit mod
        putStrLn "Eager JIT Result:"
        print res
