# DrawIR advanced interpreter spec exceeds CPU guard

## Status

Open. Rendering correctness is not disproved, but the full suite cannot serve
as timely verification evidence in interpreter mode.

## Reproduction

```sh
build/native_probe/simple test \
  test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl \
  --mode=interpreter
```

Observed on 2026-08-11: repository `kill_simple_monitor` terminated the test at
277 seconds with exit 143 while it consumed 94.7% CPU. No assertion result was
emitted before termination.

## Rendering impact

The campaign cannot use this invocation to prove DrawIR damaged replay,
embedded-surface fallback, or 8K/80 behavior. Interpreter duration is not a
native performance measurement and must never be promoted as one.

## Required resolution

Split retained-damage and embedding fallback cases into focused specs with
bounded fixtures, and run their pixel-parity oracle on an admitted native
compiler artifact. Preserve the full suite as broad coverage, but give it an
explicit measured timeout budget. A completion receipt must still report
7680x4320, p95, fallback, completion, presentation scope, and pixel checksum.

The bounded 8x6 follow-up spec now exists at
`test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_replay_spec.spl`.
Its interpreter import/setup still exceeded a 120-second outer timeout. Native
execution is separately blocked by the runner delegation defect recorded in
`native_test_runner_delegates_to_rust_seed_despite_simple_binary_2026-08-11.md`.
