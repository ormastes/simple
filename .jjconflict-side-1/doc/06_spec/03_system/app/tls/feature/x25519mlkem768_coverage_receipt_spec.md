# x25519mlkem768_coverage_receipt_spec

> Behavior contract for fail-closed X25519MLKEM768 coverage receipts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x25519mlkem768_coverage_receipt_spec

Behavior contract for fail-closed X25519MLKEM768 coverage receipts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | `doc/02_requirements/nfr/x25519mlkem768_acceleration.md` |
| Plan | `doc/03_plan/sys_test/x25519mlkem768_acceleration.md` |
| Design | `doc/05_design/x25519mlkem768_acceleration.md` |
| Source | `test/03_system/app/tls/feature/x25519mlkem768_coverage_receipt_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

Behavior contract for fail-closed X25519MLKEM768 coverage receipts.

The scenarios call the exported parser, composer, and renderer APIs. They use
typed manifests plus measured decision/condition fixtures; implementation-text
inspection is deliberately outside this system contract.

## Scenarios

### X25519MLKEM768 measured coverage receipt behavior

#### should accept only the exact provenance-bound CLI and run manifest

- Parse the canonical typed CLI
- Reject duplicate and unbound caller-controlled switches
- Accept the complete v2 manifest and reject forged execution state
- manifest text replace
- manifest text replace


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse the canonical typed CLI")
val args = ["--raw-coverage", "build/evidence/run/coverage.sdn",
    "--run-manifest", "build/evidence/run/run_manifest.env",
    "--critical-inventory", "build/evidence/run/critical.psv",
    "--compiler-artifact", "build/evidence/run/simple",
    "--runtime-artifact", "build/evidence/run/libsimple_runtime.a",
    "--output-dir", "build/evidence/run/receipt"]
expect(x25519_mlkem768_parse_coverage_receipt_cli(args).is_ok()).to_be(true)
step("Reject duplicate and unbound caller-controlled switches")
expect(x25519_mlkem768_parse_coverage_receipt_cli(
    args + ["--raw-coverage", "again"]).is_err()).to_be(true)
expect(x25519_mlkem768_parse_coverage_receipt_cli(
    args + ["--allow-unbound", "true"]).is_err()).to_be(true)
step("Accept the complete v2 manifest and reject forged execution state")
val manifest_text = _valid_manifest_text()
expect(x25519_mlkem768_parse_coverage_run_manifest(
    manifest_text).is_ok()).to_be(true)
expect(x25519_mlkem768_parse_coverage_run_manifest(
    manifest_text.replace("fallback_used=false", "fallback_used=true")
).is_err()).to_be(true)
expect(x25519_mlkem768_parse_coverage_run_manifest(
    manifest_text.replace("spec_4_outcome=passed", "spec_4_outcome=failed")
).is_err()).to_be(true)
```

</details>

#### should compose measured owner outcomes and render bound provenance

- Compose all twenty-three measured owners and critical outcomes
-  valid cli
-  critical inventory
   - Expected: receipt.owners.len() equals `23`
   - Expected: receipt.branch_outcome_total equals `118`
   - Expected: receipt.branch_outcome_covered equals `118`
   - Expected: receipt.branch_coverage_basis_points equals `10000`
   - Expected: receipt.critical_outcome_total equals `118`
   - Expected: receipt.composer_source_sha256.len() equals `64`
   - Expected: receipt.contract_source_sha256.len() equals `64`
- Render compiler runtime validator composer and contract identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compose all twenty-three measured owners and critical outcomes")
val result = x25519_mlkem768_compose_coverage_receipt_from_text(
    _valid_cli(), _valid_manifest(), _HASH_A, _measured_raw(),
    _critical_inventory(), _HASH_A)
expect(result.is_ok()).to_be(true)
val receipt = result.unwrap()
expect(receipt.owners.len()).to_equal(23)
expect(receipt.branch_outcome_total).to_equal(118)
expect(receipt.branch_outcome_covered).to_equal(118)
expect(receipt.branch_coverage_basis_points).to_equal(10000)
expect(receipt.critical_outcome_total).to_equal(118)
expect(receipt.composer_source_sha256.len()).to_equal(64)
expect(receipt.contract_source_sha256.len()).to_equal(64)
step("Render compiler runtime validator composer and contract identity")
val rendered = x25519_mlkem768_render_coverage_receipt(
    receipt, "build/evidence/run/zero.psv", _HASH_A,
    "build/evidence/run/source.env", _HASH_A,
    "build/evidence/run/spec.env", _HASH_A, _HASH_A)
expect(rendered).to_contain("measurement_status=measured")
expect(rendered).to_contain("owner_count=23")
expect(rendered).to_contain("compiler_provenance_sha256=" + _HASH_A)
expect(rendered).to_contain("runner_sha256=" + _HASH_A)
expect(rendered).to_contain(
    "coverage_composer_source_sha256=" + receipt.composer_source_sha256)
expect(rendered).to_contain(
    "coverage_contract_source_sha256=" + receipt.contract_source_sha256)
```

</details>

#### should reject a missing owner and an uncovered critical outcome

- Reject a measured stream with an empty owner denominator
-  valid cli
-  critical inventory
- Reject a required condition outcome with a zero count
-  valid cli
-  critical inventory


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject a measured stream with an empty owner denominator")
val missing = x25519_mlkem768_compose_coverage_receipt_from_text(
    _valid_cli(), _valid_manifest(), _HASH_A, _measured_raw(13),
    _critical_inventory(), _HASH_A)
expect(missing.is_err()).to_be(true)
expect(missing.unwrap_err().code).to_equal(
    "coverage-owner-denominator-empty")
step("Reject a required condition outcome with a zero count")
val uncovered = x25519_mlkem768_compose_coverage_receipt_from_text(
    _valid_cli(), _valid_manifest(), _HASH_A, _measured_raw(-1, 0),
    _critical_inventory(), _HASH_A)
expect(uncovered.is_err()).to_be(true)
expect(uncovered.unwrap_err().code).to_equal(
    "critical-branch-below-100-percent")
```

</details>

#### should enforce the 98 percent threshold for every owner independently

- Accept the boundary and reject a diluted low-coverage owner
   - Expected: x25519_mlkem768_owner_coverage_reason(98, 100) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept the boundary and reject a diluted low-coverage owner")
expect(x25519_mlkem768_owner_coverage_reason(98, 100)).to_equal("")
expect(x25519_mlkem768_owner_coverage_reason(97, 100)).to_equal(
    "branch-coverage-owner-below-98-percent:9700")
expect(x25519_mlkem768_owner_coverage_reason(0, 0)).to_equal(
    "coverage-owner-outcome-count-invalid")
```

</details>

#### should reject malformed measured input before rendering a receipt

- Reject an absent decision-condition extension
-  valid cli
-  critical inventory
- Reject an unbound critical inventory digest
-  valid cli
-  critical inventory


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject an absent decision-condition extension")
val malformed = _measured_raw().replace(
    "coverage_extension: decision-condition-v1\n", "")
val malformed_result = x25519_mlkem768_compose_coverage_receipt_from_text(
    _valid_cli(), _valid_manifest(), _HASH_A, malformed,
    _critical_inventory(), _HASH_A)
expect(malformed_result.is_err()).to_be(true)
expect(malformed_result.unwrap_err().code).to_equal(
    "raw-coverage-extension-invalid")
step("Reject an unbound critical inventory digest")
val unbound = x25519_mlkem768_compose_coverage_receipt_from_text(
    _valid_cli(), _valid_manifest(), _HASH_A, _measured_raw(),
    _critical_inventory(), "not-a-sha256")
expect(unbound.is_err()).to_be(true)
expect(unbound.unwrap_err().code).to_equal(
    "critical-branch-inventory-sha256-invalid")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** ``doc/02_requirements/nfr/x25519mlkem768_acceleration.md``
- **Plan:** ``doc/03_plan/sys_test/x25519mlkem768_acceleration.md``
- **Design:** ``doc/05_design/x25519mlkem768_acceleration.md``


</details>
