# Published Windows Phase2 cycle 1 — repair checkpoint

Status: **INCOMPLETE**. Stage2 f749 was admitted; Phase2 full CLI failed;
no real Phase2 test Results/counts and no Stage3 admission exist for this lane.

## Frozen producer and failed run

- Source HEAD: `f749c494d1dee0ad14b0e8d2f5caa6d3cf459133`.
- Admitted compiler SHA256:
  `0d4134f1328b5197036fa76be067b5f88c9eee9b13015ad44a6cd40dd1d5ce74`.
- Admission SHA256:
  `bf6e0acf1cefac6c7f1e6b60dcb6859f5d2d07f7d25db70ad03527496a15bb80`.
- Full CLI: FAIL, exit 1, 1,270 seconds, ten failed source files. Runner and
  remaining matrix were intentionally cancelled. Outer shell exit 0 after
  Windows process cancellation is not completion evidence.
- Full failure/cancellation details remain under
  `build/mini_builds/phase2-published-<compiler-sha256>/FAILURE-HANDOFF.md` and
  `build/bootstrap-published-f749c494/phase2-cancellation.env`.

## Astra source/cache lane

1. Manifest optional delimiter indices now explicitly default to -1 before
   arithmetic. Native probe: **25 compiled, zero failed; three runtime checks
   PASS**, 12.2 seconds. Evidence: `build/p2r/version-manifest/cycle1.log`.
   Executable SHA256:
   `b466b3e378857987303c1a218bbc610ac6b2c6706d2f318351e2d6b177385e3b`.
2. BYL static registry import points to the tracked compiler backend owner.
   Independent source review accepted; no separate whole-registry native
   execution is claimed.
3. Semver legacy enum spelling/type ownership and digit parsing repaired;
   Range appended without changing old ordinals; modern consumer explicitly
   imports the same owner and handles Range. Initial session stopped at its
   three-cycle cap with one of 34 runtime checks failing. A separately
   authorized resumed diagnostic identified assertion 23: strict Greater
   incorrectly accepted equal versions because of nested optional tuple
   matching. Explicit nested optional matches repair the comparator while the
   general compiler defect is tracked separately. The one corrective rerun
   **passed 40 runtime checks**, two compiled/three cached/zero failed, 9.8s.
   Evidence: `build/p2r/semver/resumed-fixed-20260923.log`; executable SHA256
   `81effe4b6fdc6dd1453bb218aedb99b4a56534671d86e0f95821c671ab38a533`.
   All original evidence and rejected binaries remain preserved in that folder.
4. Cache persist failures used 288-character object paths and existing parents.
   A two-unit native probe persisted a 356-byte object at 109 characters with
   no cache warnings and executed successfully. Evidence:
   `build/p2r/cache-check/RESULT.md`. Proposed next private roots are
   `D:/p2-20260923/c` and `/w`; preserve the full phase/compiler/runtime/entry
   identities and bind provenance before launch. No old cache was deleted.

## Other lanes and remaining gates

Formula source partition passed independent mechanical review and compiled to
object in about 75 seconds instead of the prior 600-second per-file timeout.
Link exposed nine runtime symbols. `host-gpu` deliberately selects core-C;
symbols present in native_all do not authorize a Rust runtime fallback. Eight
real core-C providers and the existing SIMD search source-list entry have now
passed source review. The hardened C selfcheck executed with exit 0 and
`PASS rt_core_c_formula_symbols_selfcheck`; its executable SHA256 is
`0fd936caa8ec634c1722af6a0a960519aec9ccd873bdf0458b2ba0955094d18c`, and its
private archive SHA256 is
`16ea2864f76903a693c859a88ba4037e28d8efc154928341847bf5517b5b3984`.
The source owner confirmed these bytes match the tested final source. The
tool receipt retained stdout/exit evidence; no standalone selfcheck log exists.
The retained real Formula probe resolves the eight new providers but still
fails on SIMD search because the old admitted producer freezes its old C source
list. A fresh producer is required. This is not a Formula runtime PASS.
The reused noncryptographic LCG remains unsynchronized (unlike the Rust mutex
implementation); CSPRNG failure injection and POSIX execution remain unverified.

HIR owner fixes and GUI field accessor repair have separate review/evidence.
GUI percentage-vs-coordinate inconsistency is tracked in
`doc/08_tracking/bug/editor_dock_zone_units_inconsistent_2026-09-23.md`; no GUI
behavior PASS follows merely from compilation.

Preserve frozen admission/capsule and all debug caches. Source repairs require
review, scoped commits and a **fresh matching Stage2 admission**, then real
full-CLI/runner Phase2 Results with nonzero counts, then Stage3. Main alone
schedules those runs and handles publication. This checkpoint is not a release
or bootstrap-completion claim.
