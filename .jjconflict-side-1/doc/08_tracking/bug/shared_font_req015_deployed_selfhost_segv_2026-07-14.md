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

The tracked deployed CLI crash is now proven to be the stale two-argument
`rt_env_set` artifact ABI documented in
`deployed_selfhost_env_set_miscompile_segv_2026-07-14.md`. The current caller
correctly supplies `(key_ptr, key_len, value_ptr, value_len)`; the old linked
callee treats `key_len=27` as the value pointer and faults at `strlen(0x1b)`.
This is not a font-source failure.

A fresh minimal stage compiler is not a full test CLI. The bounded current-source
rebuild additionally exposed a bootstrap-parser rejection and a full-CLI
closure/runtime link gap. The narrowed focused test entry then exposed a
bootstrap entry-HIR handoff failure; it now carries the entry HIR explicitly in
`CompileContext`, but the bounded build cap ended before native proof. None is a
valid replacement for deployed pure-Simple verification.

The subsequent isolated proof with the latest pure-Simple stage-55 driver also
timed out after 30 minutes with no log, cache file, candidate, or executable
font-spec result. It retained no positive evidence and was not retried.

## Required fix/evidence

Fix and redeploy the pure-Simple CLI, then run each once:

1. the focused font configuration unit spec;
2. focused Engine2D and Engine3D configuration specs;
3. the shared-font surfaces SSpec and regenerated manual;
4. the existing shared multilingual GPU-font performance collector.

Do not use `src/compiler_rust/target/**/simple` to close this bug.
