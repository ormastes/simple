<!-- codex-design -->
# Bootstrap compiler/backend stage split architecture

## Decision

Separate compiler convergence from tool assembly. Stage 3 is the final compiler
build; Stage 4 consumes that compiler rather than generating it again.

```text
Rust authority -> Stage 1 Simple seed
  -> Stage 2 Cranelift pure-Simple compiler
  -> Stage 3 LLVM pure-Simple compiler + CompilerArtifactManifestV1
  -> Stage 4 tool objects + verified link -> full CLI
```

`CompilerArtifactManifestV1` owns compiler archive/interface hashes,
compiler/runtime ABI versions, source closure, backend/target, and producer.
`ToolingLinkReceiptV1` owns tool closure, imported compiler interface, object
hashes, final binary, and `compiler_sources_compiled = 0`.

Stage 4 cannot traverse compiler sources. Any compiler, runtime, loader,
weaving, ABI, or interface mismatch invalidates Stage 3 and returns control to
Stages 2/3. A full rebuild remains a separate equivalence lane.

Implementation starts only after one admitted success of the current pipeline;
that result is the behavioral and provenance baseline.
