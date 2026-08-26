# UTF-8, internationalized text, and shared rendering evidence contract

> This scenario is for text, compiler, localization, Engine2D, Engine3D, and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# UTF-8, internationalized text, and shared rendering evidence contract

This scenario is for text, compiler, localization, Engine2D, Engine3D, and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/utf8_internationalized_text_architecture.md |
| Plan | doc/03_plan/sys_test/utf8_internationalized_text_architecture.md |
| Design | doc/05_design/lib/text_i18n/utf8_internationalized_text_architecture.md |
| Research | doc/01_research/lib/text_i18n/simple_utf8_internationalized_text_architecture_2026-08-25.md |
| Source | `test/03_system/app/text_i18n/feature/utf8_internationalized_text_architecture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

This scenario is for text, compiler, localization, Engine2D, Engine3D, and
release owners. It verifies that the full acceptance matrix remains explicit,
complete, and fail-closed before native evidence is admitted.

## Preconditions

- Run from the repository root with the pure-Simple test runner.
- Required physical backends remain required when unavailable; inventory is
  not execution evidence.
- Production correctness remains in focused owner specs and conformance suites.

## Compatibility and limitations

This source-contract scenario does not claim Unicode conformance, rendering
pixels, native device submission, or performance results. Those claims require
source-hash-bound owner coverage and matched-host receipts accepted by the
contracts exercised here.

## Overview

The workflow begins with the pinned multilingual font manifest because face
identity and source hashes are prerequisites for reproducible shaping. It then
admits only exact-face shaping witnesses, checks that Engine2D and Engine3D
remain consumers of one font-material owner, enumerates selected composite
program rows, and finally keeps physical-device evidence mandatory.

The scenario validates three durable contracts:

1. every changed text, codec, parser, i18n, Draw IR, font, Engine2D, Engine3D,
   and SIMD owner stays in the branch-coverage denominator;
2. every scalar, SIMD, parser, localization, 2D, and 3D performance row stays
   represented with an explicit evidence class;
3. zero-allocation and matched-baseline memory constraints fail when even one
   byte appears above a zero baseline or outside an allowed growth budget.

## Operator workflow

Run the scenario first to validate the matrix. Run focused owner correctness
and conformance suites next. Collect performance receipts only after correctness
passes. Bind every receipt to source, configuration, manifest, corpus, machine,
toolchain, hardware, profile, and active backend identities. Compare only
matched identities. Native-device rows additionally require submission,
completion, and device-origin readback; enumeration or CPU fallback is invalid.

## Syntax and examples

The normal acceptance command is:

```text
bin/simple test test/03_system/app/text_i18n/feature/utf8_internationalized_text_architecture_spec.spl --mode=interpreter --no-cache
```

Generate this manual with:

```text
bin/simple spipe-docgen test/03_system/app/text_i18n/feature/utf8_internationalized_text_architecture_spec.spl --output doc/06_spec --no-index
```

The inventory assertions use concrete counts and named rows. They never convert
an unavailable backend into a skip or a pass. Memory gates treat a baseline of
zero as an invariant: the after value must also be zero regardless of the
percentage allowance.

## Evidence and provenance

The executable source is the authority for scenario behavior. The requirements
and plans above define the broader production obligations. Retained receipts
must use schema `text-i18n-perf-v1`; coverage manifests must use schema
`text-i18n-branch-coverage-v1`. A receipt without exact hashes or execution
identity fails before its measurements are considered.

## Findings and remediation

- A missing owner requires updating the immutable coverage inventory and adding
  owner-focused branch tests before acceptance.
- A missing backend row remains blocked until an admissible native host and
  forced-backend or native-device run exists.
- A latency improvement accompanied by a memory regression fails the combined
  gate; neither dimension compensates for the other.
- A source-contract pass is prerequisite evidence only. It cannot replace
  Unicode conformance, parser differential, rendered-pixel, or device evidence.
- Reviewers must retain raw receipts and hashes beside the summarized result.
- Any unresolved evidence row remains visibly blocked through release review.

## Scenarios

### UTF-8 internationalized text architecture evidence

#### should retain the complete fail-closed acceptance flow

- Load the pinned multilingual font manifest
   - Expected: coverage.actual_owner_count equals `TEXT_I18N_COVERAGE_OWNER_COUNT`
- Accept exact-face-bound simple-script shaping
   - Expected: backend_rows.len() equals `TEXT_I18N_BACKEND_ROW_COUNT`
- Prepare one shared font batch for 2D and 3D
   - Expected: perf_rows[10].id equals `engine2d_cpu`
   - Expected: perf_rows[14].id equals `engine3d_hud_cpu`
   - Expected: perf_rows[15].id equals `engine3d_world_cpu`
- Emit the selected font composite program and plan compilation
   - Expected: perf_rows[11].evidence_class equals `native-device`
   - Expected: perf_rows[12].evidence_class equals `native-device`
   - Expected: perf_rows[13].evidence_class equals `native-device`
- Prove native submission and device readback
   - Expected: perf_rows[16].evidence_class equals `native-device`
   - Expected: perf_rows[17].evidence_class equals `native-device`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the pinned multilingual font manifest")
val coverage = text_i18n_coverage_contract_check(text_i18n_coverage_owners())
expect(coverage.valid).to_be(true)
expect(coverage.actual_owner_count).to_equal(TEXT_I18N_COVERAGE_OWNER_COUNT)

step("Accept exact-face-bound simple-script shaping")
val backend_rows = text_i18n_backend_rows()
expect(text_i18n_backend_contract_valid(backend_rows)).to_be(true)
expect(backend_rows.len()).to_equal(TEXT_I18N_BACKEND_ROW_COUNT)

step("Prepare one shared font batch for 2D and 3D")
val perf_rows = text_i18n_required_perf_rows()
expect(text_i18n_perf_rows_valid(perf_rows)).to_be(true)
expect(perf_rows[10].id).to_equal("engine2d_cpu")
expect(perf_rows[14].id).to_equal("engine3d_hud_cpu")
expect(perf_rows[15].id).to_equal("engine3d_world_cpu")

step("Emit the selected font composite program and plan compilation")
expect(perf_rows[11].evidence_class).to_equal("native-device")
expect(perf_rows[12].evidence_class).to_equal("native-device")
expect(perf_rows[13].evidence_class).to_equal("native-device")

step("Prove native submission and device readback")
expect(perf_rows[16].evidence_class).to_equal("native-device")
expect(perf_rows[17].evidence_class).to_equal("native-device")
```

</details>

#### should reject incomplete owner backend and performance inventories

- Reject incomplete evidence before acceptance


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject incomplete evidence before acceptance")
expect(text_i18n_coverage_contract_check([]).valid).to_be(false)
expect(text_i18n_backend_contract_valid([])).to_be(false)
expect(text_i18n_perf_rows_valid([])).to_be(false)
```

</details>

#### should enforce zero-baseline memory behavior

- Apply the deterministic no-allocation memory gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply the deterministic no-allocation memory gate")
expect(text_i18n_growth_within(0, 0, 0)).to_be(true)
expect(text_i18n_growth_within(1, 0, 100)).to_be(false)
expect(text_i18n_growth_within(101, 100, 0)).to_be(false)
expect(text_i18n_growth_within(101, 100, 1)).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/utf8_internationalized_text_architecture.md`
- **Plan:** `doc/03_plan/sys_test/utf8_internationalized_text_architecture.md`
- **Design:** `doc/05_design/lib/text_i18n/utf8_internationalized_text_architecture.md`
- **Research:** `doc/01_research/lib/text_i18n/simple_utf8_internationalized_text_architecture_2026-08-25.md`


</details>
