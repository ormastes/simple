# macOS Stage3 full-graph HIR crashes with SIGSEGV after 104 of 848 modules

Status: FIX-IMPLEMENTED-VERIFICATION-PENDING (bug_db id `stage3_macos_full_graph_hir_sigsegv_2026_09_21`)
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

## Fix implemented (2026-11-03, opus-macos-hir) — verification pending on macOS

Acting on Hypothesis A. The crash site is unknown, so no guard was added at a
guessed HIR site (a guard on the wrong operation would only hide the fault).

- **Seed gate:** `bootstrap_seed_has_aggregate_nil_fix`
  (`scripts/bootstrap/bootstrap-seed-handoff.shs`) refuses the seed handoff
  unless the seed source's `codegen/llvm/functions/objects.rs` carries the
  `2c89727c11c` select (`src_is_valid, tagged, src_tagged, "aggcopy_result"`).
  Content-keyed, so rebased/cherry-picked fixes pass. A Stage2 built by a
  pre-fix seed can no longer be produced by the sanctioned bootstrap.
  Test: `scripts/bootstrap/tests/seed-aggregate-nil-fix-gate-test.shs`
  (before: exit 127, function absent; after: PASS 4 cases).
- **macOS spec:** `test/01_unit/compiler/bootstrap/nil_optional_aggregate_copy_macos_spec.spl`
  (`# @tag:macos`) — nil `Optional<aggregate>` through a call, struct copy and
  array; 3/3 pass on Windows x86_64.

### macOS repro / check steps (Mac checker)

1. On aarch64-apple-darwin, at current `release/1.0.0` (contains `2c89727c11c`),
   rebuild the seed: `cd src/compiler_rust && cargo build --release --bin simple`;
   confirm `grep -c 'src_tagged, "aggcopy_result"' compiler/src/codegen/llvm/functions/objects.rs` = 1.
2. Rebuild Stage2 from that seed via `scripts/bootstrap/bootstrap-from-scratch.sh`
   (the handoff gate must pass).
3. Native-build and run the macOS spec with that Stage2; all 3 examples must pass.
4. Run Stage3 under lldb: `lldb -o run -o bt -o quit -- <stage2> <stage3 args from the Stage3 command transcript>`;
   keep `~/Library/Logs/DiagnosticReports/*.ips` and the lldb `bt` output.
5. Stage3 passes 848/848 HIR modules -> close as fixed. A SIGSEGV again ->
   Hypothesis A is false; attach the backtrace to this doc and reopen.
