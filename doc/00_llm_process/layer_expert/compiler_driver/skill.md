# Compiler Driver Layer Expert

## Role

Own source discovery, import closure, phase orchestration, execution-mode
selection, and compiler-driver performance under `src/compiler/80.driver/`.

## Source-loading invariant

- `Check` mode loads only the requested checking scope.
- `Interpret` mode keeps the explicit entry bounded and lets the interpreter
  module loader resolve imports lazily.
- Native entry-closure mode loads the transitive closure selected by
  `SIMPLE_NATIVE_BUILD_ENTRY` and suppresses whole-project bulk loading.
- Other project compilation modes may bulk-load the self-hosted compiler roots
  where their global compilation model requires it.

Do not reuse the native-only entry-closure environment flag as a shortcut for
interpretation: downstream HIR/MIR branches attach native/bootstrap semantics
to it. Keep the interpret exclusion explicit in
`driver_source_pipeline_loading.spl`.

## Performance evidence

For a one-file interpreted entry, measure wall time and max RSS through the
normal `bin/simple` command. A run that never reaches user code is source-loader
cost, not workload cost. Preserve the normal CPU guard; raising it is diagnostic
only and cannot be passing evidence.

Focused contract:
`test/01_unit/compiler/driver/interpret_lazy_project_sources_spec.spl`.
MCP end-to-end witness:
`test/02_integration/app/mcp_stdio_integration_spec.spl`.

Typed-storage native codegen freezes deep-copied module-qualified evidence
before cache lookup. The parent then creates class-handle MIR+storage capsules;
the builder callback sees only the frozen batch and module name. Revalidate
complete MIR/storage identity before and after codegen, bind object bytes and
size in the result receipt, and publish cache checkpoints only through the
parent completion hook. Do not call this real concurrency: the current
builder branch batches sequentially, and process workers need a complete codec.
