# Stage 2 full-graph HIR: `unresolved name: exit` in traceability/query_main.spl

- Date: 2026-11-06
- Status: OPEN — blocked: reproduces only in the full `compiler_cli_build` graph (Stage 2 verification)
- Priority: P0 (blocks Stage 2 `compiler_cli_build` verification)
- Tree: `a58d06d80d3` (ancestor of `origin/release/1.0.0`)
- Cluster: A (import/symbol resolution) with probable cluster B (HIR cache/codec) involvement

## Symptom

```
[hir-fatal] source_idx=28 path=src/app/traceability/query_main.spl error_idx=0 text=HIR lowering error in
src/app/traceability/query_main.spl: unresolved name: exit at src/app/traceability/query_main.spl:74:5
```

Log: `/private/tmp/boot4-out/s2/stage2-compiler-tests/aarch64-apple-darwin/verification/logs/compiler_cli_build.log`
(line 36844). `query_main.spl:13` has `use std.io_runtime.{exit}`; `src/lib/io_runtime.spl:16` re-exports
`exit` `from nogc_sync_mut.io_runtime`; `src/lib/nogc_sync_mut/io_runtime.spl:555` defines `pub fn exit` and
exports it at `:778`. The import is legitimate.

## Evidence

1. Same failing binary (`stage2/aarch64-apple-darwin/simple.rejected`), `compile --format=smf`:
   - minimal repro (`use std.io_runtime.{exit}` + `exit(code)`) clears HIR (fails later at llc only);
   - standalone `compile src/app/traceability/query_main.spl` clears HIR (no `exit` error); fails later in MIR.
   So the facade chase works in isolation — the failure is specific to the 3060-module graph.
2. The full-graph log has 2511 `[hir-reexport-chase-unresolved]` receipts, **none** for `item=exit`, and none
   with `facade=lib.io_runtime`. The chase either was never reached or the module surface arrived differently.
3. Span mismatch: the real call `exit(code)` is at line **119**:5 at `a58d06d80d3`, the error says **74**:5
   (column matches). Only 21 of the first 119 lines are blank/comment, so it is not comment-stripped counting.
4. The line immediately before the fatal is a HIR cache decode refusal:
   `[hir-cache-store] refused reason=decode ... enum wire enum allocation failed line=69544/70908 module=src/app/cli/cli_helpers.spl`.

## Suspects (ranked)

1. HIR cache/codec transport delivering a corrupted or stale `query_main` lowering/surface (fits the span
   mismatch and the adjacent decode refusal) — cluster B.
2. Silent skip of the `std.io_runtime` import when the module key resolves to `""` only in the full graph.
3. Module-key collision for `std.io_runtime` in the full graph (less likely: should have emitted a receipt).

## Related, not fixed here

- `test_runner_build` "unsupported LLVM value conversion from i64 to void" at
  `test_runner_mcdc_report.spl:104/113/129` persists with PR #7235 already in-tree (`a58d06d80d3`); those lines
  are `while`/`if` conditions, not `.unwrap()` bindings — a separate MIR/codegen class.
- Standalone `query_main` compile surfaces `facade=lib.common.crypto.sha1 item=list` chase misses and MIR
  `unresolved method call get/to_text/to_array` in `sha1.spl`/`sdn_codec.spl` — likely the next blocker.

## Next step

Rerun the Stage 2 `compiler_cli_build` with `SIMPLE_BOOTSTRAP_DIAG=1` and the HIR cache disabled; if `exit`
resolves, hand to cluster B (codec). Do not patch `query_main.spl`.

## Follow-up (2026-11-06, static)

- Cluster B ruled out the HIR cache: query_main was freshly lowered (`cached=0`, log 36843-36844), and
  `hir_cache_key` hashes source sha256. Suspect 1 above is withdrawn.
- The `[hir-reexport-chase-unresolved]` receipts just before the fatal (`facade=app.io.__init__`
  `item=rt_file_rename|rt_timestamp_now`) all have `importer=src/app/io/cli_*.spl`. No receipt in the log names
  `importer=.../traceability/...` or `item=exit`. query_main does not import `exit` via `app.io` or
  `nogc_async_mut.io` (its only `exit` source is `use std.io_runtime.{exit}`), so those chase misses do not
  explain a missing binding in query_main.
- Span: no tracked file has `    exit` at line 74 col 5, and there is only one `query_main.spl`. Line 119 minus
  (16 comment + 5 blank) lines is not 74, and there are no docstrings. So the line is mis-mapped, not
  stale source. Mapping not found statically.
- Remaining suspects: (a) the `std.io_runtime` import is silently skipped (empty module key) only in the full
  graph; (b) a surface or registry-generation mismatch, which takes the `reexport-root-reject` paths. Those only
  print under `SIMPLE_BOOTSTRAP_DIAG=1`, and that was off for this run. Next run: set `SIMPLE_BOOTSTRAP_DIAG=1`
  and grep `reexport-root-reject|reexport-chase\] .*wanted=exit`.
