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

## Landed so far (2026-08-18, updated end of session)
## Landed so far (2026-08-18)
- Gate: `scripts/check/check-no-direct-rt.shs` — ratchet mode (baseline
  `scripts/check/no_direct_rt_baseline.txt` = **12821**, only goes down) +
  `--critical`/`SIMPLE_RT_CRITICAL=1` phase-A error mode (any forbidden site
  fails); FAIL prints fix-it guidance. Wired into
  `scripts/check/pre-push-conflict-tree-guard.shs` (line 837, "direct rt_*
  call-site ratchet"). Re-measured 2026-08-18 end of session: 14799 files
  scanned, 12829 forbidden product sites — **8 over the 12821 baseline,
  currently FAILING** — with 7817 allowed provider references (live numbers,
  reproduce with `sh scripts/check/check-no-direct-rt.shs`; do not trust a
  stale count here without re-running it).
- Comparator: `binary_layout.spl` `compare_word` (8/8 spec green,
  `binary_compare_spec.spl`).
- **Binary SSpec is now COMPLETE across domains** (goal 4/6): protocol
  (TCP/UDP/IPv4 — `binary_domains_spec.spl` +
  `binary_protocol_domains_spec.spl`), algorithm (SHA-256/CRC32 —
  `binary_algorithm_domains_spec.spl`), embedded (UART register bit-tables —
  `binary_embedded_domains_spec.spl`), and cipher/compress (pre-existing in
  `binary_domains_spec.spl`) — all under
  `test/01_unit/lib/common/spec/evidence/`. Plus a new DECLARATIVE generation
  layer, `src/lib/common/spec/evidence/format/layout_schema.spl`: a
  `WordLayout` declared once derives words/masks/labeled diffs instead of
  hand-building a `BinaryLayout` beside a separate policy list, with an SDN
  round-trip (`layout_to_sdn`/`layout_from_sdn`); proven parity-equal to the
  hand-built TCP fixture in
  `test/01_unit/lib/common/spec/evidence/binary_layout_schema_spec.spl`.
  Usage guide extended with a "Declarative layouts" section and the
  algorithm-domain `reserved_field`-vs-`dont_care` pitfall:
  `doc/07_guide/infra/sspec/binary_sspec_usage.md`.
- `gzip_validate` now verifies **CRC32 + ISIZE** trailer fields (fail-closed),
  closing the structural-only gap recorded in
  `doc/08_tracking/bug/gzip_validate_structural_only_no_crc_2026-08-18.md` —
  see `20bbf622e88 fix(gzip): verify CRC32 + ISIZE trailer in validation`.
- C-MIG-0001 (crc32_text): differential 5/5, regression 35/35, perf spec
  `test/05_perf/lib/crc32_text_c_vs_simple_perf_spec.spl` (interpreter-lane
  ceiling only; native parity pending). **C-MIG registry now runs through
  C-MIG-0027** (`char_from_code`, differential 6/6) — 588-line registry
  `doc/08_tracking/c_migration/c_migration_inventory.sdn`; C-MIG-0013 was
  deleted from the registry. See also the dispatch-dead C function audit
  (`9980d16801e docs(c-mig): dispatch-dead C function audit — 23 dead / 343
  live-other-lane`) and codegen-lane perf re-measures: base64url
  array-accumulator 44.7x -> **35.05x codegen lane, still OPEN**
  (C-MIG-0023), utf8 batched-ASCII fast path 16.6x -> **8.27x codegen lane,
  still OPEN** (C-MIG-0022), and the time-utils 3.18x anomaly **resolved as
  an ARTIFACT** of per-call clock-probe overhead, not a real JIT regression
  (`48500ace49d`). New Fix-test standard and C-migration test standard:
  `doc/03_plan/infra/binary_runtime_hardening/plan.md`.
- Track B (parallel-agent wave): rt_migration_cycle.shs `TB_TABLE` now has
  **20 symbol→wrapper rows** (time_now_unix_micros, file_exists,
  file_delete, env_get, getpid, process_run, file_copy, thread_sleep/
  sleep_ms, get_args, file_write/file_write_bytes, env_set, dir_exists,
  dir_create_all, file_append_text, process_is_running, dir_list, dir_walk,
  platform_name, hash_text); Track C (rt_file_read_text coalesced), Track D
  (text/bytes signature-exact).
- Compiler fixes proving the alias lane: strict-JIT fail-open closed;
  bare-assignment locals minted correctly (both in `src/compiler_rust`,
  deployed binary still needs rebuild+deploy to pick up the second).
