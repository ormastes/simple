# SpirvBuilder drops its whole module to the interpreter via an unresolved JIT symbol

**Filed:** 2026-08-11
**Impact:** cost roughly four hours across two lanes before being diagnosed

## Symptom

Every spec exercising `SpirvBuilder` times out. Observed verdicts, in order:

```
reason=daemon-worker-timeout budget_ms=119970     # test daemon's 120s worker cap
reason=child-timeout budget_ms=900000             # after --no-session-daemon --timeout 900
```

The second one occurred in a *clean* checkout (`/mnt/fast/simple`) with none of the
tree's merge conflicts, so the tree state was not the cause. During the run the
child sat at ~100% of one core (measured: 2,024 CPU ticks in 20s) with buffered
output — computing, not deadlocked.

## Cause

`bin/simple run` on any module touching `SpirvBuilder` prints:

```
[jit-fallback] unresolved external symbol 'SpirvBuilder_dot_create': whole module
dropped to the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1
to turn this into a hard error.
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile:
Module error: unresolved external symbol 'SpirvBuilder_dot_create' would NULL-jump
in JIT; deferring to interpreter
```

The static method `SpirvBuilder.create` does not resolve as a JIT symbol, so the
**whole module** — not just that call — falls back to the tree-walk interpreter at
a self-reported 100–1000× penalty. A spec that builds a few SPIR-V modules then
cannot finish inside any reasonable budget.

## Why it was hard to see

The fallback is a warning on stderr among roughly 1,900 lines of lint/gc warnings,
and the resulting failure surfaces as a *timeout*, which reads as "the spec is too
big" rather than "this module is running interpreted". Two lanes independently
concluded their own logic was at fault:

- one restructured its spec repeatedly across six runs
- the other split its spec in two, which helped only because the fast half no
  longer touched `SpirvBuilder`

Note the diagnostic value of `timeout=1` verdicts: they are *not* evidence about
the code under test, in either direction. That rule is what eventually pointed at
the harness rather than the spec.

## Workaround

Prove `SpirvBuilder` behaviour outside the spec harness: a small script via
`bin/simple run` that prints `build()`, piped to the real Khronos tools. Slow
(interpreted) but bounded, and it is how the SPIR-V conformance evidence in
`board_vulkan_spirv_khronos_conformance_2026-08-11.md` was obtained.

## Unblock condition

Resolve `SpirvBuilder_dot_create` as a JIT symbol so the module JIT-compiles.
Verify with `SIMPLE_JIT_STRICT=1`, which turns the silent fallback into a hard
error and would have surfaced this immediately. Then re-run
`test/01_unit/os/vulkan/spirv_khronos_validation_spec.spl` — that spec exists and
is believed correct, but has never produced a non-timeout `Results:` line.

Worth considering separately: a silent 100–1000× fallback is a poor default for a
test lane. Making `SIMPLE_JIT_STRICT=1` the default under `bin/simple test` would
convert a mysterious timeout into a named error.

## Status

Open. Not a defect in `SpirvBuilder`'s SPIR-V output, which is proven conformant
under Khronos SPIRV-Tools v2025.1 — this is purely a JIT symbol-resolution gap.
