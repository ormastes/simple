# Compiler Architecture TLDR

Compiler architecture is the stable source-to-artifact pipeline. Shared
frontend and IR contracts feed multiple backends; target/runtime policy is
validated before artifacts reach startup or tests.

```text
Source
  -> Frontend(AST)
  -> HIR + Types + Semantics
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
- Keep strict runtime-family and no-allocation checks on target-sensitive paths.

Open next:

- `00_compiler_architecture.md`
- `compiler/mdsoc/mdsoc_architecture_tobe.md`
- `compiler/backend/unified_backend_architecture.md`
- `compiler/backend/runtime_backend_completion_audit.md`

