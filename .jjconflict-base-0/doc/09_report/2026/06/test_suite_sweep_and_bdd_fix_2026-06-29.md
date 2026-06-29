# Full-suite test sweep + fixes — 2026-06-29

## Update (later 2026-06-29): second systematic fix + decisive categorization

**Fix #2 landed — cross-module array write-back lost in BDD closures.** A
cross-module function that builds a `[u8]` via an in-place append helper returns
a TRUNCATED array only when called from a BDD it-block (correct from main).
Converted `encoding/{msgpack,bson,cbor}` append helpers to return-based +
reassign — all three specs now **0 failures** (commits `f81e3804`, bson/cbor
follow-up). Seed bug filed:
`doc/08_tracking/bug/interp_crossmodule_array_writeback_lost_in_bdd_closure_2026-06-29.md`.

**lib/common after both fixes:** 484 pass / 125 fail / 23 err (23 err = WARN/INFO
noise). Decisive breakdown of the 125 remaining FAIL files:
- **~62 `wine_*`** (wine_process 29, wine_dll 12, wine_kernel32_* 6, wine_nt/ntdll 7,
  wine_hello 3, …): **59 are "function not found"** — a test-first Windows
  PE-loader / NT / kernel32 / ntdll emulation suite with **no implementation**.
  NOT bugs; implementing them is a large unrequested feature.
- **~18 other missing-symbol**: `set_utils`/`iterable`/`functions` modules were
  **deliberately deleted** (commit "Track production readiness convergence");
  the specs (incl. `deprecated_removed_spec`, `iter_deprecated_spec`) are **stale**
  → removal needs approval, not restore.
- **~45 genuine value-mismatch**: encoding cluster now FIXED; `lshr/overflow_debug`
  are scratch specs expecting logical `>>` when i64 `>>` is correctly arithmetic
  (spec wrong, not a bug); the rest is a long individual tail (each its own
  investigation).

**Conclusion:** the two systematic clusters (BDD matcher + cross-module array
write-back) are fixed. The literal "fix ALL" is blocked by: unbuilt features
(Wine), deliberately-removed-API stale specs (approval to delete), and a
heterogeneous individual tail — no third silver bullet.

## Fixes landed (verified)
1. **BDD matcher bug** (seed, commit `62cea5b`, rebuilt+deployed) — `expect(falsy_call()).to_matcher()`
   false-failed ("expected call result to be truthy"). Monotonic `BDD_MATCHER_RAN` flag.
   **Dominant cause: ~70% of unit-test failures.** lib/common ~32%→~10%. No false-greens
   (genuine mismatches and bare hollow `expect(call())` still fail).
2. **Encoding guard reverts** — revived 9 deleted `*_guard_spec.spl` + restored 8 sources + yaml/parse.spl.
3. **Compress guard reverts** — restored 10 sources (3 had jj conflict markers).
4. **Test-runner refuse→fallback** (commit `e17778`) — bulk runs no longer false-fail 0/N.
5. Restored deleted `bin/simple` symlink (a parallel session wiped it mid-session).

## Sweep methodology
Per-file `<release-binary> run <spec>` at `-P 16` (absolute path — symlink got clobbered once).
Excludes hidden `.spipe_*` fixture files (not standalone tests). 16,780 real spec files.
(Bulk `simple test <dir>` halts after "Session setup" — unresolved; per-file is the only reliable path.)

## FINAL full-suite results (ALL 16,780 real spec files completed)
- **PASS 13,391 (80.7%)**, FAIL 2,541, ERR 670, timeout/noresult 178.
- **FAIL+ERR = 19.3%** of files. (ERR is mostly import/JIT *warnings* masking the result + some
  real module-resolution errors; system/perf specs are environment-heavy: QEMU, Lean/Mathlib.)
- Note: `test/01_unit/*` and `test/unit/*` are parallel near-duplicate trees (similar per-dir
  failure counts), so ~half the 16,780 is duplication.
- Method: `<release-binary> run <spec>` per file, -P 16→24, 30–60s timeout, absolute binary path
  (symlink got clobbered mid-run by a parallel session and was restored).

## Failure distribution (by dir, reliable sample)
lib 319, os 143, integration/app 132, unit/app 128, compiler 73, system/app 67,
system/check 35, browser_engine 17, browser 12, formal_verification 12.

## Residual failure classes (heterogeneous — no second silver bullet)
- **Unimplemented-API specs**: e.g. `compress_utilities_spec` imports ~22 functions
  (`write_u16_le`, `decode_match_extension_length`, …) that don't exist in `compress.utilities`
  — written test-first against an unbuilt module.
- **Toolchain-dependent**: Lean/Mathlib (`expected import Mathlib...`), QEMU system specs.
- **Seed/interpreter bugs**: `with_module_name not found on dict`, i64::MIN negation overflow.
- **Slow specs** hitting the 60s per-file timeout (os/system).
- A few genuine value mismatches.

Each needs individual investigation; fixing the full ~12k baseline is multi-session work.
The one high-leverage fix (matcher) is done and resolves the largest share.
