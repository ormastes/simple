# Vacuous-Spec Sweep — "literal-only, zero-import" family (2026-08-18)

Measurement round only. **No spec file was edited.** Cross-referenced against
`doc/08_tracking/test/spec_vacuity_families_full_corpus_census.md` (families 3/4/5).
That census's `NOSRC` bucket (2,597 dedup files importing nothing, flagged
`[LOW PRECISION]`) is the superset of this family; this sweep is the missing
precision pass: it intersects zero-import with *literal-driven assertions* and
ranks by blast radius.

## Method

Driver: `awk` structural scan of all `test/**/*_spec.spl`, deduped by content
`md5sum` (the numbered/unnumbered twin trees, e.g. `test/unit` vs `test/01_unit`,
otherwise double-count everything).

Per file measured: `it "…"` examples; `use` lines; `expect|check|assert`
statements; assertions whose subject is a variable assigned a **string literal**
earlier in the file (or a bare `"lit".contains(...)`); and a purity flag for
`read_file|read_text|read_to_string|read_lines|fs.read|File.open|run_command|spawn|exec_`.

**Corpus:** 20,543 spec files raw -> **10,743 after content dedup**;
**117,062 declared examples**, **318,220 assertions**.

## False positives avoided (explicitly)

- **Disk-reading specs excluded.** Any file touching `read_file`/`read_text`/
  `File.open`/`run_command`/`spawn` is dropped from the ranking — asserting on
  real file content is a genuine source-level check, per the brief.
- **Computed values excluded.** Only assertions whose subject variable was
  assigned a literal *in the same file* count; `expect(f(x)).to_equal("lit")`
  where `f` is imported never counts, because the subject is a call.
- **Golden/snapshot tests excluded** by the same rule — the rendered side is a
  call result, not a literal-assigned variable.
- **Numeric literals deliberately EXCLUDED from the headline number.** A second
  pass including them yields 532 files / 3,886 examples, but it over-counts:
  `val a = 5; expect(a + 3).to_equal(8)` genuinely exercises the arithmetic
  evaluator. The string-literal ranking below is the high-confidence set.
- **Positive control:** the detector independently re-finds the known case —
  `test/unit/compiler/mir/bitfield_mir_spec.spl` (the still-unfixed twin of the
  already-repaired `test/01_unit/...` copy) ranks #18 at 19 examples / 0 imports
  / 38 of 40 assertions literal-driven.

## Repo-wide totals (measured, deduped)

| bucket | files | declared examples |
|---|---|---|
| zero `use` lines **and** >=1 example | 1,978 | 23,599 |
| imports only `std.spec`/`std.test` (nothing subject-related) | 797 | 7,839 |
| **TIER 1 — zero-use + majority literal-driven + no file/proc IO** | **423** | **1,537** |
| of TIER 1, 100% of assertions literal-driven | 371 | 457 |

**1,541 assertions across 1,537 declared examples are structurally incapable of
failing.** The wider zero-import population (23,599 examples) cannot reach any
subject module by import, but many reach builtins (`text`, arithmetic) and so
are not all vacuous — that is why TIER 1 is the actionable number.

## Ranked TIER 1 — worst 30 by (examples x vacuity ratio)

| # | path | examples | imports | asserts | literal-driven asserts | verdict |
|---|---|---|---|---|---|---|
| 1 | `test/01_unit/compiler/backend/riscv32_asm_spec.spl` | 79 | 0 | 88 | 54 | PARTIALLY VACUOUS |
| 2 | `test/01_unit/compiler/parser/error_recovery_intensive_spec.spl` | 81 | 0 | 114 | 58 | PARTIALLY VACUOUS |
| 3 | `test/01_unit/compiler/native/inline_asm_spec.spl` | 41 | 0 | 55 | 52 | PARTIALLY VACUOUS |
| 4 | `test/unit/lib/common/string_spec.spl` | 46 | 0 | 59 | 39 | PARTIALLY VACUOUS |
| 5 | `test/01_unit/compiler/native/inline_asm_constraints_spec.spl` | 30 | 0 | 36 | 35 | PARTIALLY VACUOUS |
| 6 | `test/01_unit/lib/common/string_spec.spl` | 47 | 0 | 62 | 38 | PARTIALLY VACUOUS |
| 7 | `test/02_integration/compiler/parser_integration_spec.spl` | 45 | 0 | 55 | 35 | PARTIALLY VACUOUS |
| 8 | `test/01_unit/app/tooling/html_utils_spec.spl` | 44 | 0 | 75 | 48 | PARTIALLY VACUOUS |
| 9 | `test/02_integration/compiler/lexer_integration_spec.spl` | 42 | 0 | 47 | 30 | PARTIALLY VACUOUS |
| 10 | `test/01_unit/lib/i18n/resource_bundle_spec.spl` | 33 | 0 | 63 | 51 | PARTIALLY VACUOUS |
| 11 | `test/03_system/feature/app/native_exe_spec.spl` | 47 | 0 | 63 | 35 | PARTIALLY VACUOUS |
| 12 | `test/01_unit/app/tooling/markdown_utils_spec.spl` | 37 | 0 | 65 | 44 | PARTIALLY VACUOUS |
| 13 | `test/01_unit/app/tooling/format_utils_spec.spl` | 36 | 0 | 77 | 51 | PARTIALLY VACUOUS |
| 14 | `test/01_unit/app/test_runner_new/test_categorization_spec.spl` | 37 | 0 | 55 | 34 | PARTIALLY VACUOUS |
| 15 | `test/01_unit/compiler/parser/error_recovery_simple_spec.spl` | 37 | 0 | 58 | 33 | PARTIALLY VACUOUS |
| 16 | `test/01_unit/app/mcp_unit/mcp_cli_tools_spec.spl` | 21 | 0 | 22 | 21 | PARTIALLY VACUOUS |
| 17 | `test/03_system/hardware/riscv64_fpga/manifest_format_spec.spl` | 24 | 0 | 28 | 22 | PARTIALLY VACUOUS |
| 18 | `test/unit/compiler/mir/bitfield_mir_spec.spl` | 19 | 0 | 40 | 38 | PARTIALLY VACUOUS |
| 19 | `test/03_system/hardware/riscv64_fpga/hello_payload_spec.spl` | 18 | 0 | 39 | 39 | VACUOUS |
| 20 | `test/system/hardware/riscv64_fpga/hello_payload_spec.spl` | 18 | 0 | 31 | 27 | PARTIALLY VACUOUS |
| 21 | `test/01_unit/compiler/shb/shb_extractor_spec.spl` | 21 | 0 | 23 | 17 | PARTIALLY VACUOUS |
| 22 | `test/01_unit/app/search/search_spec.spl` | 19 | 0 | 21 | 15 | PARTIALLY VACUOUS |
| 23 | `test/01_unit/app/sdn_spec.spl` | 22 | 0 | 30 | 17 | PARTIALLY VACUOUS |
| 24 | `test/01_unit/compiler/native/baremetal_syntax_spec.spl` | 14 | 0 | 14 | 12 | PARTIALLY VACUOUS |
| 25 | `test/01_unit/compiler_core/branch_coverage_32_spec.spl` | 19 | 0 | 24 | 15 | PARTIALLY VACUOUS |
| 26 | `test/03_system/hardware/riscv64_fpga/jtag_unbind_spec.spl` | 12 | 0 | 20 | 19 | PARTIALLY VACUOUS |
| 27 | `test/system/app/native_build/feature/executable_size_reduction_spec.spl` | 11 | 0 | 11 | 11 | VACUOUS |
| 28 | `test/03_system/hardware/riscv64_fpga/hardware_inventory_spec.spl` | 11 | 0 | 23 | 23 | VACUOUS |
| 29 | `test/03_system/app/native_build/feature/executable_size_reduction_spec.spl` | 11 | 0 | 11 | 11 | VACUOUS |
| 30 | `test/01_unit/compiler/native/asm_match_spec.spl` | 12 | 0 | 44 | 37 | PARTIALLY VACUOUS |

(Full ranked list regenerable by re-running the driver; 423 rows total.)

## What these numbers do and do not establish

**Do establish (structural, mechanical):** these files declare no imports, so no
`use`-resolved subject module is reachable; and the named fraction of their
assertions has a subject that is a string literal written in the same file.
Deleting the module the filename advertises cannot turn any TIER 1 file red.

**Do NOT establish:** semantic vacuity. A grep/awk sweep cannot prove an
assertion is a tautology — it can only show the subject is literal by
construction. Specifically unproven here: (a) whether builtins reached without
`use` (text methods, operators) make an assertion meaningful; (b) whether a
spec's *describe* text is honest about its subject; (c) mutation-testing
evidence — the only proof of failability is deleting the subject and observing
red, which this round did not run. (d) The purity filter is a name-based
denylist; a spec doing IO through an unlisted helper would be misclassified.

**Recommended next round:** mutation-check the top 30 (delete/rename the subject
module, confirm the spec stays green), then rewrite in filename order.
