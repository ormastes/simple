# compiler

Single source of truth for the Simple compiler implementation.

## Current status

- `src/compiler/` is the active compiler codebase for frontend, type system, MIR, backend, linker, and bootstrap flow.
- `src/compiler_core/` has been retired and removed.
- Bootstrap scripts and docs now target `src/compiler/`.

## Bootstrap summary

```
seed.cpp (C++ seed compiler)
  -> compiles core runtime/compiler entry
  -> produces initial native compiler
  -> compiler recompiles itself for reproducibility
```

## Notes

- Shared cross-cutting modules remain in `src/compiler_shared/` and `src/llvm_shared/`.
- Legacy desugared-core tooling notes are historical and should not be used as the primary build path.
