# Seed: a 1500-arm value `match` chain stalls (no output in 300 s)

**Date:** 2026-11-27
**Status:** FIXED (2026-11-27) — JIT-only; quadratic-or-worse liveness solver
**Component:** Rust seed (`src/compiler_rust`), JIT/run path

## Symptom

A value-position `match` with ~1500 arms (`[]` arms, final arm `xs`) produces
no output within 300 s on BOTH seed `simple-local-20261127m.exe` and
`...127p.exe`. The same shape with 100 / 300 / 700 arms runs in ~160-220 ms,
so growth is not linear in that range: something goes superlinear (or loops)
between 700 and 1500 arms. Not caused by the weak-empty join change (seed m
stalls identically).

## Probes

`long*.spl` in the reviewer scratch dir
`C:\Users\yoon\AppData\Local\Temp\claude\07e8ec21a8a8dcf3\1357817b-c723-4b2e-821a-ee9cf4f2a43c\scratchpad\mt2\`.

## Suspects (unverified)

`lower_match_arms` (hir/lower/expr/control.rs) recurses once per arm and now
also walks the else chain in `hir_value_is_concrete` per level (quadratic in
arm count; but m, without that walk, stalls too, so the stall predates it).
Needs a profile before any fix.

## Root cause (found 2026-11-27)

Layer: JIT codegen, NOT parse/HIR. `SIMPLE_EXECUTION_MODE=interpret` runs the
1500-arm probe in ~150 ms; `jit` stalls (cliff between 900 arms ~230 ms and
1100 arms >100 s, with RSS growing to >4 GB). An lldb stack of the stalled seed
sits in `MirFunction::compute_live_ins` (`mir/function.rs`) called from
`codegen::instr::body::compile_function_body`.

The solver was a round-robin sweep to a fixed point. A value-position `match`
lowers to a nested if/else chain whose merge blocks are created BEFORE the
inner else-chain blocks, so the block vector is in reverse flow order and each
sweep propagated liveness one hop: N sweeps x N blocks x per-block set clones.

## Fix

`compute_live_ins` now uses a predecessor-driven worklist (revisit a block only
when a successor's live-in changed). Regression test:
`test_compute_live_ins_long_reverse_ordered_chain` (5000-block reverse-ordered
chain) in `compiler/src/mir/function.rs`.

## Second cause and final result

After the liveness fix a 1100-arm match still took 10 s (stack in
`cranelift_frontend::SSABuilder::seal_one_block`): `compile_function_body`
translated blocks in storage order and sealed ALL blocks at the end, so every
cross-block `use_var` was resolved through the whole chain. Now (non-generator,
non-async functions) blocks are translated in reverse post-order and each block
is sealed once all its predecessors are emitted; the liveness worklist is also
seeded in post-order.

JIT timings (seed r before -> seed t after), 1500 arms: >300 s -> 3.0 s.

| arms | r (before) | t (after) |
|---|---|---|
| 100 | 0.2 s | 0.4 s |
| 700 | 0.3 s | 0.25 s |
| 900 | 0.23 s | - |
| 1100 | >100 s | 2.0 s |
| 1500 | >300 s | 3.0 s |
| 3000 | - | 9.2 s |

Interpret mode was never affected (~150 ms at 1500). Residual: growth from
1100 to 3000 arms is still mildly superlinear (~n^1.5); not profiled further.
Seed t: `C:/dev/keep/seeds/simple-local-20261127t.exe`.
