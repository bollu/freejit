FreeJIT
=======

A WIP experiment to try and JIT free monads.

Idea is to be like accelerate, but to try and piggy back on Polly's GPGPU
code generation computation capabilities to automatically detect parallelism.


## What works
- "Free monad" can now JIT
- Problem is, it doesn't support the usual way of encoding "next state" computation:
  cannot do:
```hs
data Lang next = Get Key (\Value -> next) | ...
```


## Roadmap
- [x] Get **some** JIT working
- [ ] Use Template Haskell to JIT the same code at compile time 
- [ ] Inspect functions at compile time to JIT the `Get` kind of computations


## Papers
- Type-safe Runtime Code Generation: Accelerate to LLVM
- [Defunctionalizing Push arrays](https://svenssonjoel.github.io/writing/defuncEmb.pdf)
