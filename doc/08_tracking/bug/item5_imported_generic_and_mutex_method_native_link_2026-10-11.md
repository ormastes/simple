# Item 5 native dynlib link: imported generic and mutex methods

Status: OPEN (2026-10-11). The imported generic call has a source-level candidate fix; no current-source native PASS yet.

## Reproducer and evidence

The four-module dynlib gate command is retained at `build/mini_builds/item5_dynlib_gate_new_mono_20261011/run.sh`. It uses the current pure-Simple Stage 2 candidate and one-binary LLVM/core-C. The generated native objects in `build/mini_builds/item6_cas_explicit_copy_20261010/cache/se1eae4c6b9886f50f8e4d1a40fcf257b/` show the exact mismatch:

- The mutex owner object defines `lib.nogc_sync_mut.concurrent.mutex.mutex_new$i64` and `lib.nogc_sync_mut.concurrent.mutex.mutex_unlock$i64`.
- The dynlib snapshot registry object references bare `mutex_new$i64` and `mutex_unlock$i64`, although it references the qualified `lib.nogc_sync_mut.concurrent.mutex.mutex_lock_gate`.
- The dynlib lifetime object references `lib.nogc_sync_mut.concurrent.mutex.Mutex.lock` and `lib.nogc_sync_mut.concurrent.mutex.Mutex.unlock`, which remain undefined in the four-module link.

`monomorphize_integration.spl` now selects the generic template's declaring module for rewritten cross-module call names. The two-module unit spec asserts exact qualified names, and `test/fixtures/compiler/mono_imported_global/` provides a native imported-global reproducer. The old Stage 2 binary cannot validate this source change: it does not expose `run` or `check`; the root `bin/simple` in this checkout resolves to a Rust bootstrap seed and fails while parsing a separate current-source file, so that result is not a qualification.

## Required closure

1. Rebuild a pure-Simple compiler from this source when the host has bootstrap headroom, then run the focused unit spec and imported-global native fixture.
2. Re-run the four-module dynlib gate and confirm the two generic references resolve to the owner symbols.
3. Trace and fix the independent `Mutex.lock` / `Mutex.unlock` emission failure, then pass the native dynlib fixture, Item 5 acceptance, and matched size/startup/RSS cohorts.

At evidence capture the filesystem had 6.7 GB free, below the bootstrap minimum. No Item 5 pass or size claim follows from this candidate.

## 2026-10-11 current-source HIR probe

A 300-module native probe now compiles the edited monomorphizer source through HIR and monomorphization. Explicit types for seven indexed transient-owner promotions cleared an unrelated `E-MONO-032` gate; the final pass reported 60 generic call sites, 38 specializations, and zero unresolved. The native-build worker then crashed with signal 11 in MIR, before link or the exact-name assertions could run. The three-cycle limit is exhausted; see [the MIR worker bug](item5_mono_hir_probe_mir_worker_crash_2026-10-11.md). The generic symbol fix remains unqualified.
