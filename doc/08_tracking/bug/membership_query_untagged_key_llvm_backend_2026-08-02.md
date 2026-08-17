# Membership queries (.contains/.has/in): untagged needle in the seed LLVM backend

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Date:** 2026-08-02 · **Severity:** medium (latent — lane not currently shipped) · **Area:** seed LLVM codegen

## Status of the family

Collections store boxed/tagged values (`rt_value_*`, ints as `k<<3`), so a
membership query must wrap the needle the same way before calling
`rt_contains`, or answers are wrong in both directions (raw `k` misses the
stored `k<<3`; a raw `8` finds a stored `1`).

- **Cranelift/JIT: FIXED 2026-08-01** (`wrap_value` → `rt_value_int`,
  `common_backend.rs` P0 note).
- **Interpreter / spec lane / native worker: correct or fail-closed** —
  probe truth table 2026-08-02 (hand-computed expectations incl. `k<<3`
  discriminator keys): dict `contains_key`/`has`, `arr.contains`, `x in arr`
  all PASS under interpreter, JIT and `bin/simple test`; the native worker
  fails closed ("MIR unresolved method call: contains") rather than lying.
- **Seed LLVM backend: was untagged at 4 emit sites; 3 FIXED 2026-08-02**
  via type-gated `build_wrap_membership_needle` (static int →
  `rt_value_int`, bool → `rt_value_bool`, float → boxed, unknown/heap left
  untouched — no double boxing; the pre-boxed MIR dict path is untouched):
  1. `codegen/llvm/functions/calls.rs` `bare_rt_redirect` "contains"
  2. same file, `qualified_rt_redirect` "contains|contains_key|has_key|has"
  3. `codegen/llvm/functions.rs` BuiltinMethod arm
  4. **OPEN:** `codegen/llvm/emitter.rs:1443` trait emitter — the
     `CodegenEmitter` trait carries no vreg type info; an unconditional wrap
     would corrupt text/pre-tagged needles. Needs its own lane.

## Verification bounds

`cargo check -p simple-compiler --features llvm --release` and the release
driver build are clean, and all probes re-pass against the rebuilt seed. The
fixed LLVM lane itself is NOT end-to-end exercisable on this host: the
release seed ships without the `llvm` feature, `native-build` delegates to
the pure-Simple worker, and the `SIMPLE_BOOTSTRAP=1` replay dies on an
unrelated `'span'` semantic error. Behavioral proof needs an llvm-feature
seed build.

## 2026-08-17 re-classification (lane s2_rust_codegen) — NOT in the silent-wrong-result class

This row was swept as part of the "CORE + P1 + silently wrong results" batch. It
does not belong to that class, by this doc's own evidence (line 21): the seed
LLVM backend **fails closed**, raising `MIR unresolved method call: contains`,
rather than returning a wrong answer.

That makes it a loud, self-announcing capability gap — the opposite of the defect
class being hunted, which compiles clean, exits 0, and hands back a wrong result.
It is still a real open gap and should stay open, but it should not be
prioritised or triaged as a silent-miscompile row.

No source change made. No reproduction attempted, because a fail-closed
diagnostic needs none.

## Content re-verification 2026-08-17 (m2_rust_compiler lane) — ALREADY-FIXED

`src/compiler_rust/compiler/src/codegen/llvm/emitter.rs:323` now maps
`"contains" | "contains_key" | "has_key" | "has" => Some("rt_contains")`, with a
unit assertion at `emitter.rs:2328`. The documented behaviour was a fail-CLOSED
gap ("MIR unresolved method call: contains") rather than a miscompile; the method
is now resolved, so the gap is closed rather than a wrong answer being fixed.
Not runtime-verified on this host (no seed cargo build under the live bootstrap).
