# REQ-015 deployed self-host verification exits 139

Status: open

## Impact

The shared multilingual GPU-font runtime configuration implementation and its
focused Simple specs cannot be accepted or performance-baselined with the
required pure-Simple tooling. This blocks REQ-015 executable evidence and the
font performance rerun; it does not justify using the Rust seed as a substitute.

## Reproduction

From `/tmp/simple-font-publish` at `e2edf611653` plus the REQ-015 working diff:

```text
bin/release/simple test test/01_unit/lib/common/text_layout/font_render_config_spec.spl --mode=interpreter
exit=139

bin/release/simple check src/lib/nogc_sync_mut/text_layout/font_types.spl
prints: Checking src/lib/nogc_sync_mut/text_layout/font_types.spl...
exit=139
```

The freshly built `build/bootstrap-font-fresh-origin-stage55/simple` also exits
139 for the single-file check. Its `test` invocation treats the SSpec as an
ordinary source file, so it is not a valid replacement for the deployed full
CLI.

## Required fix/evidence

Fix and redeploy the pure-Simple CLI, then run each once:

1. the focused font configuration unit spec;
2. focused Engine2D and Engine3D configuration specs;
3. the shared-font surfaces SSpec and regenerated manual;
4. the existing shared multilingual GPU-font performance collector.

Do not use `src/compiler_rust/target/**/simple` to close this bug.
