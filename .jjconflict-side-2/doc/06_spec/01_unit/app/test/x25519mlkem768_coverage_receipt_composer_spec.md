# X25519mlkem768 Coverage Receipt Composer Specification

> Tests covering X25519MLKEM768 coverage receipt composer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Coverage Receipt Composer Specification

## Scenarios

### X25519MLKEM768 coverage receipt composer

#### parses only the exact typed CLI surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--raw-coverage", "build/evidence/run/coverage.sdn",
    "--run-manifest", "build/evidence/run/run_manifest.env",
    "--critical-inventory", "build/evidence/run/critical.psv",
    "--compiler-artifact", "build/evidence/run/simple",
    "--runtime-artifact", "build/evidence/run/runtime.a",
    "--output-dir", "build/evidence/run/receipt"]
expect(x25519_mlkem768_parse_coverage_receipt_cli(args).is_ok()).to_be(true)
expect(x25519_mlkem768_parse_coverage_receipt_cli(
    args + ["--raw-coverage", "again"]).is_err()).to_be(true)
expect(x25519_mlkem768_parse_coverage_receipt_cli(
    args + ["--allow-unbound", "true"]).is_err()).to_be(true)
expect(x25519_mlkem768_parse_coverage_receipt_cli(
    args + ["--compiler-version", "forged"]).is_err()).to_be(true)
```

</details>

#### accepts a complete provenance-bound run manifest and rejects absence

- valid run manifest text
- valid run manifest text


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = x25519_mlkem768_parse_coverage_run_manifest(
    valid_run_manifest_text())
expect(parsed.is_ok()).to_be(true)
expect(x25519_mlkem768_parse_coverage_run_manifest(
    "schema=simple-native-coverage-run-v2\nstatus=measured\n").is_err()).to_be(true)
expect(x25519_mlkem768_parse_coverage_run_manifest(
    valid_run_manifest_text().replace("spec_4_outcome=passed", "spec_4_outcome=failed")
).is_err()).to_be(true)
```

</details>

#### composes exact twenty-three-owner measured outcomes

- valid cli
- critical inventory
   - Expected: receipt.owners.len() equals `23`
   - Expected: receipt.branch_outcome_total equals `118`
   - Expected: receipt.branch_outcome_covered equals `118`
   - Expected: receipt.branch_coverage_basis_points equals `10000`
   - Expected: receipt.critical_outcome_total equals `118`
   - Expected: receipt.composer_source_sha256.len() equals `64`
   - Expected: receipt.contract_source_sha256.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = x25519_mlkem768_compose_coverage_receipt_from_text(
    valid_cli(), valid_manifest(), HASH_A, measured_raw(),
    critical_inventory(), HASH_A)
expect(result.is_ok()).to_be(true)
val receipt = result.unwrap()
expect(receipt.owners.len()).to_equal(23)
expect(receipt.branch_outcome_total).to_equal(118)
expect(receipt.branch_outcome_covered).to_equal(118)
expect(receipt.branch_coverage_basis_points).to_equal(10000)
expect(receipt.critical_outcome_total).to_equal(118)
expect(receipt.composer_source_sha256.len()).to_equal(64)
expect(receipt.contract_source_sha256.len()).to_equal(64)
val rendered = x25519_mlkem768_render_coverage_receipt(
    receipt, "build/evidence/run/zero.psv", HASH_A,
    "build/evidence/run/source.env", HASH_A,
    "build/evidence/run/spec.env", HASH_A, HASH_A)
for id in owner_ids():
    expect(rendered).to_contain(id + "_source_sha256=" + HASH_A)
expect(rendered).to_contain(
    "critical_branch_inventory_sha256=" + HASH_A)
expect(rendered).to_contain(
    "compiler_provenance_sha256=" + HASH_A)
expect(rendered).to_contain(
    "coverage_composer_path=src/app/test/x25519mlkem768_coverage_receipt.spl")
expect(rendered).to_contain(
    "coverage_composer_source_sha256=" +
        receipt.composer_source_sha256)
expect(rendered).to_contain(
    "coverage_contract_path=src/app/test/x25519mlkem768_coverage_contract.spl")
expect(rendered).to_contain(
    "coverage_contract_source_sha256=" +
        receipt.contract_source_sha256)
```

</details>

#### rejects a missing owner and an uncovered critical outcome

- valid cli
- critical inventory
   - Expected: missing.unwrap_err().code equals `coverage-owner-denominator-empty`
- valid cli
- critical inventory
   - Expected: red.unwrap_err().code equals `critical-branch-below-100-percent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = x25519_mlkem768_compose_coverage_receipt_from_text(
    valid_cli(), valid_manifest(), HASH_A, measured_raw(13),
    critical_inventory(), HASH_A)
expect(missing.is_err()).to_be(true)
expect(missing.unwrap_err().code).to_equal("coverage-owner-denominator-empty")
val red = x25519_mlkem768_compose_coverage_receipt_from_text(
    valid_cli(), valid_manifest(), HASH_A, measured_raw(-1, 0),
    critical_inventory(), HASH_A)
expect(red.is_err()).to_be(true)
expect(red.unwrap_err().code).to_equal("critical-branch-below-100-percent")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test/x25519mlkem768_coverage_receipt_composer_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 coverage receipt composer.
- X25519MLKEM768 coverage receipt composer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
