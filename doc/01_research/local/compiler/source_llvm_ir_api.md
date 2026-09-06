# Compiler-owned source-to-LLVM IR API: local research

<!-- codex-design -->

## Current state

- `src/app/io/rt_compile_stub.spl` fabricates a successful LLVM module that
  ignores the source and always returns zero from `main`.
- The Rust seed duplicates that behavior in
  `compiler/src/interpreter_extern/native_sffi.rs`; the standalone runtime also
  publishes a zero-return ABI stub.
- Three Simple compile paths call the raw `rt_compile_to_llvm_ir` symbol and
  `app.io.__init__` re-exports the fabricated implementation globally.
- The real pure-Simple pipeline already owns parsing, HIR, MIR, borrow/async/
  optimization passes, and `MirToLlvm`, but has no result-bearing source-to-IR
  driver API.
- LLVM translation is one module at a time. Concatenating independently emitted
  LLVM modules would duplicate headers, declarations, globals, and metadata and
  is not a valid module aggregation strategy.
- `LlvmIRBuilder.create` receives a target triple but `emit_module_header`
  discards it and re-derives the header from environment state. That prevents an
  explicit API from making its target argument authoritative.

## Existing reusable boundaries

- `CompilerDriver` owns load, parse, HIR/typecheck, monomorphization, MIR
  lowering, borrow checking, async lowering, MIR optimization, AOP, and debug
  transforms.
- `MirTargetContext` can be derived from explicit target text without a tool or
  host probe.
- `LlvmTargetConfig` and `MirToLlvm` own target configuration and textual LLVM
  emission.
- The shell-based SimpleOS and bare-metal CLI paths already materialize `.ll`,
  invoke `llc`, and invoke a linker; they can naturally consume one IR unit per
  compiled source module.

## Atomic closure

The raw symbol can be removed only after all Simple callers use the
compiler-owned API, the CLI handles every returned module, the explicit target
reaches both MIR and LLVM lowering, and the pure-Simple API is reachable without
an app-to-compiler dependency. At that point the Rust interpreter registration,
runtime export, codegen signature, native-link stub allowlist entry, and common
runtime symbol entry have no remaining caller and can be deleted together.

