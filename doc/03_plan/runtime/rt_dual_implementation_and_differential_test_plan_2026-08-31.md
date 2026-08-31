# Plan: dual C + pure-Simple `rt_*` implementation, driven by a differential test corpus

**Date:** 2026-08-31
**Status:** PROPOSED — wave 1 in flight
**Scale (measured, not estimated):** 1454 `rt_*` symbols implemented in Rust only;
714 in C only; 560 in both; 1114 referenced but implemented in neither.
**Reusable oracle:** 1557 `#[test]` cases already exist in `src/compiler_rust/runtime/src/**`.

## The idea that makes this tractable

Do NOT hand-write 1454 C implementations against prose specs. The Rust runtime is
already an executable specification, and 1557 tests already encode its behaviour.
Extract those tests once into a **language-neutral scenario corpus**, then run every
scenario against all three implementations and require identical results:

    scenario (symbol, inputs, expected)
        |-- Rust runtime      (the oracle — must pass by construction)
        |-- C runtime         (new implementations)
        |-- pure Simple       (where a Simple-level implementation is meaningful)

A symbol is DONE when the same scenario set passes on every implementation that is
supposed to exist for it. Divergence is a finding, not a rounding error.

## Why this ordering

Writing implementations first and tests second reproduces the failure this repo has
already recorded: an unbacked or falsely-successful extern silently returns a
plausible wrong value and corrupts behaviour with no error
(`unregistered_extern_silent_nil_2026-08-01`). `rt_black_box` is the sharp case —
a stub that returns its argument links, passes a naive test, and silently destroys
a constant-time guarantee. The corpus must exist before the implementations, so
"it compiled" is never mistaken for "it works".

## Waves

**Wave 1 — the enablers (in flight).** Nothing else is efficient without these.
1. *Corpus extraction*: convert the 1557 Rust tests into declarative scenarios
   keyed by `rt_*` symbol. Output is data, not code, so all three runners consume it.
2. *Differential harness*: one runner that executes a scenario against Rust, C, and
   Simple and reports per-implementation pass/fail plus divergences.
3. *Coverage map*: which of the 1454 have Rust tests (free scenarios) versus which
   need scenarios authored. This partitions the work and sizes it honestly.

**Wave 2 — C implementations, by family, ranked by reference count.** Families are
the natural unit: string, array, dict, math, io, process, time, simd. Each wave-2
agent owns one family end to end: implement in C, run the family's scenarios on
both Rust and C, report divergences. Families with no scenarios get scenarios first.

**Wave 3 — pure-Simple implementations**, only where a Simple-level implementation
is meaningful. Many `rt_*` are intrinsics (raw memory, syscalls, SIMD lanes) with no
sensible Simple body; those are declaration-only BY DESIGN and are not gaps. The
C-vs-Simple census settles which is which — do not generate tasks against it until
that lands.

**Wave 4 — scenario-level parity gates.** Wire the differential harness into the
check suite so a future divergence fails a push rather than being discovered by a
Windows link three months later.

## Acceptance, per symbol

1. C implementation exists and is not platform-gated away on any supported target.
2. Scenarios pass identically on Rust and C (and Simple where applicable).
3. Edge cases are covered, not just the happy path: boundary values, overflow,
   malformed input, empty/NULL, and the documented failure mode.
4. Any deliberate divergence from Rust behaviour is recorded in the scenario file
   with its reason — silent divergence is a defect.

## Explicit non-goals

- Stubs. A link error is strictly better than a wrong value.
- Raising the ISA baseline or weakening a guard to make something link.
- Implementing symbols nothing references, purely to reach a round number.

## Known hazards, already measured on the Windows lane

- Adding a `.c` file wholesale to a build list duplicates symbols: `runtime.c`
  defines 121 `rt_*`, of which 53 collide with the core-C supplement and 69 with the
  Rust runtime. Extraction into a new TU is required (`8ca87866c6`: 475 collisions).
- `Vec4f` constructors store f64 bits per slot while generated `Vec4f.to_array`
  reads raw f32 — a live inconsistency the SIMD work had to match rather than fix.
