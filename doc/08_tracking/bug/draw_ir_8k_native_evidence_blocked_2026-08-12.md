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
