# CORRECTION (2026-08-31, after the C-vs-Simple census)

**Waves 2 and 3 below are WITHDRAWN. Dual C + pure-Simple implementation is not the
architecture, so implementing 1454 symbols in C and "all" in Simple would have been
fabricated work against the design.**

Evidence, from three primary sources rather than inference:

- `doc/02_requirements/runtime/simple_core_runtime_completeness_2026-06-02.md`:
  `simple_core` REPLACES `runtime_native.c` for the core lane, realizing "runtime in
  pure Simple, **C only where required**". Duality is a transitional frontier.
- The C-only family profile IS "where required": sdl2 66, glfw 49, audio 41, rocm 31,
  sqlite 27, opencl 26, opengl, font, win32 — C library bindings with no meaningful
  Simple body.
- `doc/04_architecture/runtime/default_native_runtime_shift_to_c_core_abi.md`:
  `simple-core` and `core-c-bootstrap` are ALTERNATIVE lanes, each linking one
  archive; `rust-hosted` is removed and fails closed.

Measured buckets (C vs pure-Simple): both 282, C-only 1,357 (by design),
Simple-only 241, neither 1,605 (feature-gated FFI, already ratcheted).

Methodology point that makes those numbers trustworthy: `extern fn rt_X(...)` is a
BINDING, not an implementation — **3,106 declarations vs 523 real Simple bodies**.
Counting declarations as implementations would have inflated the Simple side 6x and
produced a plausible, entirely wrong backlog.

## What replaces waves 2 and 3

**Gap A — finish the machine-checked contract.** `CORE_REQUIRED_RUNTIME_SYMBOLS`
(`src/compiler_rust/common/src/runtime_symbols.rs:118`) names 88 symbols; 75 exist,
**13 do not**. Ranks 1-8 are filed as
`simple_core_lane_missing_heap_registry_abi_2026-08-22.md`; 9-13 should be appended.
A finishing task with a defined end. Ranks 1-4 are unreferenced from `.spl` because
CODEGEN emits them — measured, and it inverted the census's own initial ranking.

**Gap B — the Windows-invisible 90.** 90 symbols are referenced, have their only C
definition inside a POSIX conditional, and have no Simple fallback. Absent on
Windows, and the ratchet CANNOT see them: it asks "backed anywhere?" not "backed on
this target?". Unfiled, and precisely the class this Windows lane keeps
rediscovering one link error at a time.

**Wave 1 (differential corpus) stands** — reusing the 1557 existing Rust tests
distinguishes a correct implementation from one that merely links, which matters
regardless of how many implementations exist.

---

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
