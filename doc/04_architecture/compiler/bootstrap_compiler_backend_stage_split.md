<!-- codex-design -->
# Bootstrap compiler/backend stage split architecture

## Decision

Separate compiler convergence from tool assembly. Stage 3 is the final compiler
build; Stage 4 consumes that compiler rather than generating it again.

```text
Rust authority -> Stage 1 Simple seed
  -> Stage 2 canonical pure-Simple compiler (unchanged configuration)
  -> Stage 3 canonical pure-Simple compiler (unchanged configuration) + CompilerArtifactManifestV1
  -> Stage 4 tool objects + verified link -> full CLI
```

`CompilerArtifactManifestV1` owns compiler archive/interface hashes,
compiler/runtime ABI versions, source closure, backend/target, and producer.
`ToolingLinkReceiptV1` owns tool closure, imported compiler interface, object
hashes, final binary, and `compiler_sources_compiled = 0`.

Stage 4 cannot traverse compiler sources. Any compiler, runtime, loader,
weaving, ABI, or interface mismatch invalidates Stage 3 and returns control to
Stages 2/3. A full rebuild remains a separate equivalence lane.

The Stage-3 runtime authority includes a canonical required-symbol manifest
whose hash is bound into `CompilerArtifactManifestV1`. Stage 4 compares every
required symbol with the admitted archive before linking and fails closed on
the first absence. Hosted providers, generated unresolved-symbol stubs, and
seed fallback are outside the authority. `--help`/`--version` probes run only
on the linked tool after `ToolingLinkReceiptV1` validates the runtime archive,
symbol-manifest, compiler identity, and output hashes.

Implementation starts only after one admitted success of the current pipeline;
that result is the behavioral and provenance baseline.
