# DrawIR 8K Native Evidence Blocked — 2026-08-12

The canonical retained-damage benchmark is
`test/05_perf/graphics_2d/draw_ir_damage_8k_bench.spl`. It measures twenty
7680x4320 CPU DrawIR frames with one changing 256x128 damage rectangle, keeping
seed and final full readback outside timing.

No production performance row is available on this host:

- `bin/simple_native --version` terminated with signal 11.
- `bin/simple run ...` identified itself as the Rust bootstrap seed, then its
  interpreter run was killed by the 60-second resource guard at 2,454,572 KiB
  peak RSS before producing frame results.
- A seed-driven `native-build` with entry closure, aggressive optimization,
  and `core-c-bootstrap` exceeded its explicit 300-second watchdog and produced
  no executable.

GDB localized the deployed self-hosted `--version` crash to a call through
address zero while entering `cli.main_part2.filter_internal_flags`. That helper
alone used `for arg in args`; its adjacent working flag cleaner used indexed
array traversal. The source now uses the indexed form and has a source-contract
regression. The deployed binary could not rebuild itself: its `native-build`
path separately passed a boxed value (`0x12`) to `rt_env_set` and crashed in
`strlen`. A no-stub seed-assisted build over narrowed `src/lib` roots still
timed out after 300 seconds without an artifact. Therefore the source repair is
not yet promoted as a verified self-hosted executable fix.
The encompassing CLI source-contract file currently reports 11/15 assertions
passing; four unrelated existing assertions fail, so this change has source
contract coverage but no green-file verification claim.

This blocks an honest pure-Simple DrawIR 8K/80 claim. Do not promote primitive,
interpreter, cached-replay, or compile-time observations as a frame result.
Resolution requires a verified self-hosted executable or a bounded successful
native build, followed by the benchmark's p50/p95, checksum, RSS, fallback, and
readback receipt.

## 2026-08-17 triage — BLOCKED, not re-measured in this lane

Read and left OPEN with its blocker intact. Deliberately **not** re-measured
here rather than reported on weakly: closing it requires either a working
self-hosted `native-build` or a QEMU/board evidence run, and both are outside
this lane's budget and permissions (one test process at a time, no main-compiler
build).

One relevant fact measured today that bears directly on the native-artifact half
of these blockers: `bin/simple native-build` currently fails outright on a
twelve-line struct probe with `error: semantic: undefined field 'kind': cannot
access field on value of type 'nil'` (gate:
`scripts/check/check-aot-smoke.shs` → `FAIL — AOT lane broken`). So the AOT lane
is broken ahead of any performance question — a native-renderer or DrawIR
artifact build cannot succeed while that holds, and re-attempting these
benchmarks before it is fixed would only re-derive the same blocker. Detail:
`doc/08_tracking/bug/aot_llvm_void_type_struct_probe_2026-08-10.md`.
