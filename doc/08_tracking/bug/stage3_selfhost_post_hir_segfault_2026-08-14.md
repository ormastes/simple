# Stage 3 self-host post-HIR segfault (2026-08-14)

## Reproducer

From a clean `origin/main` worktree, run:

```sh
scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --backend=cranelift --deploy --no-mcp --jobs=2
```

## Evidence

- The deployed `release/x86_64-unknown-linux-gnu/simple test --help` crashes in
  `rt_env_set` while setting `SIMPLE_TEST_DEPTH`; its value argument is the
  invalid address `0x11`.
- Bootstrap cycle 1 rejected the multiline condition in
  `typed_storage_view_producer.spl` at the newline after `dest.?` and then
  crashed rather than returning the parser diagnostic cleanly.
- Cycle 2 crashed in
  `CompileContext.error_count()` from `CompilerDriver.lower_and_check_impl`.
- Replacing those internal accessor calls with direct reads of the scalar
  owned by `CompileContext.add_error` advanced cycle 3 through the first three
  HIR modules with `error_count=0` and into backend field processing.
- Cycle 3 still ended with exit 139 later in Stage 3. The bounded build log is
  `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.

Higher-model review of the retained cycle-3 log narrows the last observable
frontier to pure-Simple MIR method-call lowering. The log ends while resolving
`push` with impossible receiver local ID `103079215111`; it contains no final
signal marker or backtrace, so this is a frontier, not a proved crash site.
Inspect receiver writeback/resolution at
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2366-2403`,
`:2542-2695`, and the push specialization at `:2961+`. The source shape active
near the frontier is the pending/visited aggregate walk at
`src/compiler/35.semantics/value_struct_layout.spl:78-117`; adjacent semantic
coverage exists at
`test/01_unit/compiler/semantics/value_struct_layout_spec.spl:172-309`.

The direct scalar reads added in
`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:353-357,449,489,505,526`
avoid the earlier invalid `CompileContext.error_count()` receiver. They do not
prove or repair the general receiver-corruption root cause. No exact native
aggregate-receiver regression exists yet.

## Required follow-up

Capture the next post-HIR backtrace in a fresh lane, fix the pure-Simple owner,
add an exact native receiver regression plus one adjacent value-struct/push
case, then prove a provenance-verified Stage 4 full CLI with
`scripts/check/check-bootstrap-essential-tools-smoke.shs`. Stage 3 is a
prerequisite, not test admission. Do not substitute the Rust seed as test
authority and do not re-run the three exhausted cycles from this lane.

## Restart12 SimpleOS evidence

The nested-guard change in
`src/compiler/60.mir_opt/mir_opt/typed_storage_view_producer.spl` passed the
former multiline parse frontier. A strict LLVM
`--full-bootstrap --full-cli --no-mcp --jobs=min` run produced admitted Stage 2
SHA-256 `9c8757a5a31d5605b8765267789e0a2d1a882523ec84c523b740ed8ed3c55d10`
and then exited 139 later in Stage 3 MIR lowering. The retained log is
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`, SHA-256
`2dceab3fd116533537826b09b49cc64acfb2bfaaad6f9e5bd4036d5dd10af263`.
This lane exhausted its third attempt and stopped WARN.
