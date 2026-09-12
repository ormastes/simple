# Site 9: Stage 2's Stage-3 route now times out in `native_compile` (status 124)

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-8, `work/bootstrap-full-6-2026-09-12` at `272482747da`,
  run `build/bootstrap-boot8a` (08:11:19 -> 08:33:13, 22m, load ~23-35, `--jobs=10`).
- Severity: **the current `--stop-after-stage2` admission blocker**, and the successor to
  site 8 (`stage2_stage3_route_segv_mir_json_shadow_witness_2026-09-13.md`, CLOSED/FIXED).
- Candidate: `build/bootstrap-boot8a/stage2/aarch64-unknown-linux-gnu/simple`, sha256
  `95763bffee64a74ee9d7c876ec27b37dc798ed9bb403ec502a8e42660388ad74`, 152199352 B
  (executable pin: `scratchpad/boot8/pin/simple.boot8.stage2`, same sha).

## The verdict, verbatim

```
Stage 2: proving struct receiver/runtime capability
error: Stage 2 struct receiver/runtime capability failed
| error: stage2 failed the positional pure-Simple Stage-3 route (status 124)
PASS — 1 check(s), stage stage2 failed (exit 3) and said why
  warning: stage2 native-build failed (exit 3); Stage 3/full CLI unavailable
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Stage-2 sanity is green on this candidate: `status=pass`, `version_output=simple-bootstrap
1.0.1-beta.1`, `frontend_smoke_status=0`, `frontend_smoke_bootstrap0_raw_status=0`,
`frontend_smoke_bootstrap1_ran=true`, `frontend_smoke_bootstrap1_raw_status=0`,
`frontend_smoke_bootstrap_mode_status=0`, `sha_stable_status=0`, `checks_run=5`.
The receiver step, which is the umbrella that CONTAINS the route probe, reports
`status=fail`, `runtime_compare_status=0`, `probe_exit=1`.

## `124` is a timeout, and the limit is the gate's own 180 s

`scripts/check/check-bootstrap-stage2-struct-receiver.shs:124` sets
`stage2_route_timeout=${STAGE2_SELFHOST_ROUTE_TIMEOUT_SECONDS:-180}` and invokes the candidate
under `timeout -k 5s "${stage2_route_timeout}s"` (`:151`). `124` is GNU `timeout`'s time-limit
exit, so the route did not fail — it was killed.

## Where it was killed, measured

`stage2-receiver.log`, last four lines:

```
[build] phase=native_cache state=running ... done=2 total=2 ... elapsed_ms=7146 current=complete
[build] phase=native_compile state=running unit_kind=modules done=0 total=2 remaining=2
        succeeded=0 cached=0 failed=0 task_done=5 task_total=6 elapsed_ms=7168 dt_ms=22
        current=compiler.common.module_path_naming
[NATIVE] codegen: 2 uncached module(s), concurrency=1
```

So the route completes `parse`, `hir`, `monomorphize`, `mir` and `native_cache` (2/2) in
**7.2 s**, enters `native_compile` on `compiler.common.module_path_naming`, and produces no
further progress line in the remaining ~173 s. Note the contrast with site 8's run, which
reached `native_compile` at `elapsed_ms=94426`: this candidate gets there 13x faster and then
stops emitting.

## What is NOT yet known

Whether this is a genuine HANG or merely slower than 180 s. A replay of the gate's exact probe
with a 2400 s ceiling is the discriminator (`scratchpad/boot8/probe9.sh`, log `probe9.log`,
`probe9.meta`); its outcome must be recorded here before anyone raises the timeout. Do NOT raise
`STAGE2_SELFHOST_ROUTE_TIMEOUT_SECONDS` to get an admission until that run says the work
terminates — a knob that hides a hang is worse than the blocked admission.

If it terminates, this is a performance defect in the pure-Simple native codegen path (2 modules
taking >3 min), and the honest fix is to make it fast enough, with the timeout raise as an
explicitly recorded interim. If it does not terminate, it is a hang in `native_compile` and needs
the same treatment site 8 got: attach, find the loop, measure.
