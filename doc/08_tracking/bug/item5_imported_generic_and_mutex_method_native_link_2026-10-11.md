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

## 2026-10-11 current-source four-module link diagnosis

A newly rebuilt pure-Simple Stage 2 candidate (SHA-256 e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06) passed parent sanity and provenance. Its outer compiler-test matrix stopped before executing at the missing explicit MC/DC-off delegation waiver; this candidate is diagnostic, not a release-qualified full CLI.

The exact four-module dynlib fixture passed HIR, monomorphization (10 generic templates, 8 call sites, 2 specializations, 0 unresolved), MIR, and LLVM codegen. Link no longer reports bare mutex_new$i64 or mutex_unlock$i64, supporting the owner-qualified call-name repair. It instead reports undefined Mutex.lock and Mutex.try_lock from the dynlib lifetime owner object; the source calls imported free mutex_new and mutex_unlock. Cranelift reached the same four modules but rejected both dynlib AOT units before link with opaque enum diagnostics. Receipts: build/mini_builds/item5_dynlib_gate_current_20261011/build.log, item5_dynlib_gate_current_llvm_20261011/build.log, and item5_dynlib_gate_ir_20261011/build.log.

Object relocations confirm the lifetime owner requests Mutex.try_lock from its module initializer and Mutex.lock from active functions. The monomorphizer NamedVar lookup checked a caller-local SymbolId before the qualified imported display name. Module-local IDs can collide with unrelated generic class methods. A source candidate now checks the display name and owner first and accepts a method SymbolId hint only when its complete method name and owner agree. A hand-built HIR regression asserts mutex_new and mutex_unlock beat colliding Mutex method IDs and that a foreign qualifier is refused. The candidate has not been rebuilt into a new Stage 2 compiler or executed; the three-cycle bootstrap limit ends another run in this session.
