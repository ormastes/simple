# macOS Stage3 full-graph HIR crashes with SIGSEGV after 104 of 848 modules

Status: OPEN (bug_db id `stage3_macos_full_graph_hir_sigsegv_2026_09_21`)
Priority: P0
Platform: aarch64-apple-darwin
Observed: 2026-09-21
Site (bug_db): `src/compiler/20.hir/hir_lowering/types.spl`

This doc was missing; created by p0f-3 from the bug_db rows (description,
evidence 0-3, next-step) so the record has a home. No new measurements.

## Facts (from bug_db)

- Source `a31729a88ed7c0b2808e5dc016c2f29bd99633a1`; the former 6 GB
  module-surface freeze was passed, HIR entered, native compiler exit 139
  (SIGSEGV) after 104/848 HIR modules, RSS max 2.44 GB, 206.84 s.
- Last log line: `phase3:hir:imports:start` for `process_governor.spl` (the
  in-flight module, not the faulting operation). `driver_phase_gates.spl` had
  emitted unresolved `BuildLinkState`, `BuildProgressState`, `OptimizationConfig`.
- No IPS/core written, so the faulting instruction is unknown.
- Bounded probes (`process_governor.spl` alone, `driver_phase_gates.spl` entry
  closure) did not reproduce.

## Analysis (2026-11-02, p0f-3)

Not reproducible on Windows x86_64; source reading only.

- **Platform-specific?** Likely, with a root shared with the other macOS Stage3
  crashes: seed-built code on aarch64 turning a nil `Optional<aggregate>` into a
  non-nil zeroed aggregate (`zerokind_is_a_corrupt_aggregate_2026-09-03.md`
  section 3a, fixed by `2c89727c11c`) or an owner payload word of 0 (guarded by
  `57271d9ba49`, see
  `stage3_streaming_hir_owner_crash_after_origin_fix_2026-08-22.md`). The
  2026-09-21 run postdates both fixes, so either the admitted Stage2 was built
  by a seed predating `2c89727c11c`, or a third aggregate-handling defect
  exists. The evidence does not say which; compare the Stage2 SHA256
  `e9ace767...` build seed date against `2c89727c11c` (2026-09-04).
- **Hypothesis A (most likely):** Stage2 built from a seed without the
  `objects.rs` fix; same corrupt-aggregate class surfacing in import resolution
  in `hir_lowering/types.spl`. Test: rebuild the seed at `release/1.0.0`,
  rebuild Stage2, rerun Stage3.
- **Hypothesis B:** import/resolution-cache lifetime across the full graph (the
  bug_db next-step compares with the BOOT-20 class-field owner bug);
  count-dependent, which would explain why bounded probes pass. The new spec
  checks index/ordered-array consistency for 848 entries on Windows and passes,
  so a plain-Simple data-structure defect is not indicated here.
- **Hypothesis C:** the unresolved `BuildLinkState` / `BuildProgressState` /
  `OptimizationConfig` names lead to a nil-typed symbol dereference once a
  resolution fails; a fail-closed diagnostic there would convert the SIGSEGV to
  an error.
- **Windows impact:** none shown; no bounded fix is possible without a fault.
- **Regression guard added:**
  `test/01_unit/compiler/bootstrap/full_graph_surface_index_lifetime_invariant_spec.spl`
  (2 examples, 0 failures on Windows x86_64).
- **Needed to repro:** a symbolized native fault on aarch64-apple-darwin (keep
  the IPS report or run under `lldb -o run`), or a fixture reproducing 104/848
  with the same module order.

Suggested bug_db status: keep open, reproducibility `target_only`.

TODO(p0f-3): obtain an IPS/lldb backtrace for the compiler process on macOS and
rerun with a Stage2 built by a post-`2c89727c11c` seed.

## Re-review (2026-11-02, opus, release/1.0.0 74cdbef8e6b)

- Darwin thread-stack difference ruled out. Phase-3 HIR runs on the main
  thread, and no runtime `pthread_create` sets a stack size. The 8 MiB Darwin
  main stack is larger than the 1 MiB Windows default, so a recursion-depth
  overflow would show up on Windows first.
- After the mono removal, the bug is neither obsolete nor confirmed. The
  failing source `a31729a` predates the monomorphization deletion, but the
  `resolve_import_symbols` path behind the last probe still exists
  (`hir_lowering/_Items/module_build.spl:320`). Validity on the current head is
  unknown.
- There is no fault, so no code change was made. Status stays `open`.
- Exact macOS repro: on aarch64-apple-darwin, rebuild the seed and Stage2 from
  `release/1.0.0`, then run
  `sh scripts/bootstrap/resume-stage3-from-admitted.sh <OUTPUT_DIR>` under
  `lldb` (or keep the ReportCrash IPS). It passes when HIR reaches 848/848; if
  it crashes, attach the symbolized backtrace here.
