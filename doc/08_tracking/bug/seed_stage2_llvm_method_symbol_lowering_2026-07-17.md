# Seed stage-2 link failure: LLVM backend misses method-call→rt_* lowering

**Date:** 2026-07-17
**Severity:** critical (the redeploy wall — blocks self-hosted bootstrap stage 2)
**Status:** FIX IN REVIEW (lane S63, wt_s58) — stage-2 relink evidence pending

## Symptom

Bootstrap stage 2 (`SIMPLE_BOOTSTRAP` forces the seed's LLVM llc path to
native-build `src/app/cli/bootstrap_main.spl`) fails at link with 67
deduplicated undefined symbols against `libsimple_native_all.a`.
Evidence log: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`.

## Root cause (scout S60 + verified S63)

WRONG-NAME problem, not a missing-runtime problem:

- 40 of the 67 are literal method-call symbols (`str.substring`, `str.bytes`,
  ...) emitted by the seed's **LLVM backend**, which lacked part of the
  method-call→rt_* interception that the **Cranelift backend** has
  (`src/compiler_rust/compiler/src/codegen/instr/calls.rs` ~3162-3200).
  The runtime archive itself is complete (rt_* definitions present; verified
  via nm — 223K+ symbols).
- Residual classes: ~11 compiler-internal names leaking to link, ~13 runtime
  functions genuinely absent or differently named, 3 alloc/memory symbols.

## Fix policy (important precedent)

Only mappings **copied verbatim from the Cranelift table** or with verified
arity+semantics AND a proven-existing runtime symbol may be added to the LLVM
`runtime_func` map (`llvm/functions.rs`). An earlier fix attempt invented
aliases (`split_whitespace→rt_string_split` — arity mismatch;
`byte_at→rt_string_char_at` — byte-vs-char semantics; targets like
`rt_string_push_str`/`rt_to_hex` that do not exist in the runtime). Such
mappings convert loud link errors into silent miscompiles and were rejected in
review. Methods with no correct runtime target stay **unmapped (loud)**:
`str.lines`, `str.parse_int_radix`, `str.push_str`, `str.to_hex`, `str.byte_at`,
`str.ord`, `str.split_whitespace`, `str.to_lowercase` — their long-term route is
a stdlib-compiled symbol (the existing `repeat → lib__common__string_core__str_repeat`
pattern) or earlier lowering.

## Verification protocol

1. Targeted cargo codegen tests (regression tests assert `bytes`/`chars` lower
   to `rt_string_bytes`/`rt_string_chars`, which exist at runtime.h:292-293).
2. Rebuild seed from fixed source; re-run ONLY the stage-2 native-build/link
   command from the log; report the actual residual undefined-symbol set.
   Expected: the 40 method-name symbols that have legitimate mappings drop;
   a residual set remains and is tracked here.

## Related

- `deployed_seed_test_runner_init_hang_2026-07-17.md` — stale seed at the
  release path; refreshed/self-hosted redeploy depends on this fix.
- `bootstrap_stage2_empty_mir_bodies_2026-07-05.md`,
  `selfhost_bootstrap_unresolved_symbols_2026-06-24.md` — earlier stage-2 walls.
