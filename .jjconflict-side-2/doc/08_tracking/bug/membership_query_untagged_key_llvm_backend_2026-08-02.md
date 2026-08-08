# Membership queries (.contains/.has/in): untagged needle in the seed LLVM backend

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
