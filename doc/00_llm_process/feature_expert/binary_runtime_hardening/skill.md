# Feature Expert — binary_runtime_pure_simple_hardening

Parent initiative unifying: SSpec binary reference (stacked layout), direct `rt_*` removal, C→Simple migration, shared HAL differential testing, and cross-language perf gates.

## Read first
- Research (frozen design): `doc/01_research/infra/sspec_binary/binary_sspec_rt_hardening_frozen_design_2026-08-18.md`
- Design: `doc/05_design/infra/sspec/binary_reference_stacked_design.md`
- Plan: `doc/03_plan/infra/binary_runtime_hardening/plan.md`
- Prior SSpec evidence design: `doc/05_design/infra/sspec/modern_sspec_typed_evidence_design.md`

## Non-negotiables for any agent working here
1. `reference Type` (resolved type, stacked default) is the only normal authoring path; `expect(actual).to_binary(expected)` is the only normal comparison.
2. Reserved ≠ don't-care. `reserved_zero/one` are checked; gray means `compare_mask = 0` under the current context only.
3. One comparator/evidence pipeline (`std.spec.binary` etc.). Never add a parallel binary diff/table helper — merge into the canonical owners.
4. No new direct `rt_*` in product code. Use the `std.*` semantic API or a sanctioned provider-only alias; the alias must be proven zero-cost by running in every lane (interpreter/JIT/AOT/native/bootstrap).
5. C removal requires: SSpec I/O differential evidence + independent oracle where available + perf verdict Faster/Equivalent (≤1.02 noise band; >2% regression = Fail).
6. Critical checkers emit measured counts, never a bare PASS; zero-scanned = ERROR.

## Canonical registries
`binary_reference_layouts.sdn`, `runtime_boundary_inventory.sdn`, `c_migration_inventory.sdn`, `cross_language_perf_results.sdn`, `binary_test_coverage.sdn` — one merge owner; Markdown lists are generated projections.

## Usage guide (goal 4/6, spec authors)
- `doc/07_guide/infra/sspec/binary_sspec_usage.md` — practical usage guide for
  `binary_layout.spl` (word-table vs plain assert, layout definition, exact
  `compare_word` precedence rules with line citations, reading a
  `stacked_compare_rows` failure, domain recipes, verified pitfalls). Read
  this before writing a new binary/protocol/cipher/register spec; it is the
  IMPLEMENTED surface (mask-aware comparator + stacked table), distinct from
  the not-yet-landed `reference Type` / `.to_binary()` authoring sugar in the
  design doc above.

## Landed so far (2026-08-18)
- Gate: `scripts/check/check-no-direct-rt.shs` — ratchet mode (baseline
  `no_direct_rt_baseline.txt`, only goes down) + `--critical`/`SIMPLE_RT_CRITICAL=1`
  phase-A error mode (any forbidden site fails); FAIL prints fix-it guidance.
  Current state: 14793 files scanned, 14241 forbidden sites (baseline
  14251), with 6697 allowed provider references.
- Comparator: `binary_layout.spl` `compare_word` (8/8 spec green,
  `binary_compare_spec.spl`).
- C-MIG-0001 (crc32_text): differential 5/5, regression 35/35, perf spec
  `test/05_perf/lib/crc32_text_c_vs_simple_perf_spec.spl` (interpreter-lane
  ceiling only; native parity pending). C-MIG inventory: 19 entries
  (2 done, 8 planned, 8 assess, 1 verified). Registry:
  `doc/08_tracking/c_migration/c_migration_inventory.sdn` + bug list
  `c_replaceable_bug_list.md` (C-MIG-0001..0020).
- Track B (parallel-agent wave): 11 symbol→wrapper rows in rt_migration_cycle.shs
  TB_TABLE (time_now_unix_micros, file_exists, file_delete, env_get, getpid,
  process_run, file_copy, thread_sleep, get_args, file_write); Track C
  (rt_file_read_text coalesced), Track D (text/bytes signature-exact).
- Compiler fixes proving the alias lane: strict-JIT fail-open closed;
  bare-assignment locals minted correctly (both in `src/compiler_rust`,
  deployed binary still needs rebuild+deploy to pick up the second).
