# Compiler Architecture TLDR

Compiler architecture is the stable source-to-artifact pipeline. Shared
frontend and IR contracts feed multiple backends; target/runtime policy is
validated before artifacts reach startup or tests.

```text
Source
  -> Frontend(AST) + Blocks
  -> HIR + Types + Semantics
  -> Monomorphization
  -> MIR + Borrow + MIR Opt
  -> Backend(C/LLVM/Cranelift/WASM/GPU)
  -> Driver artifacts + metadata
  -> Loader / interpreter / tools
```

Key rules:

- Keep parser, HIR, MIR, diagnostics, and source locations shared.
- Put backend-specific decisions behind backend contracts, not in frontend or
  semantic layers.
- Emit launch/runtime metadata for startup instead of forcing startup to guess.
- Bootstrap defaults to pure-Simple `dynload`; Rust rebuilds require
  `--full-bootstrap`.
- Treat entry-closure and native cache reuse as conservative around AOP/MDSOC,
  interpreter, loader, and compiler ABI changes.
- Build package/direct-sibling and direct-declaration-owner indexes once per
  compilation pass; HIR lowerers register only the requested sibling symbol,
  retaining the old scan only for re-export fallback and misses.
- Resolve module-qualified functions through the `SymbolTable` qualified index;
  never use a per-access full `keys()` scan.
- Keep strict runtime-family and no-allocation checks on target-sensitive paths.

Open next:

- `00_compiler_architecture.md`
- `compiler/mdsoc/mdsoc_architecture_tobe.md`
- `compiler/bootstrap_build_modes.md`
- `compiler/backend/unified_backend_architecture.md`
- `compiler/backend/runtime_backend_completion_audit.md`
