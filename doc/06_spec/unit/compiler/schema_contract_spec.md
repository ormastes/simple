# Schema Contract Specification

> Tests covering schema contract domain model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Schema Contract Specification

## Scenarios

### schema contract domain model

#### supports required and optional fields with defaults, units, identities, and field ids

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- supports required and optional fields with defaults, units, identities, and field ids
   - Expected: contract.field_count() equals `2`
   - Expected: contract.required_names() equals `["id"]`
   - Expected: contract.has_field("latency_ms") is true
   - Expected: latency.is_optional() is true
   - Expected: latency.default_value equals `0`
   - Expected: latency.unit_name equals `ms`
   - Expected: latency.min_value equals `0`
   - Expected: latency.max_value equals `1000`
   - Expected: id.identity equals `UserId`
   - Expected: id.field_id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports required and optional fields with defaults, units, identities, and field ids")
val id = schema_field_required("id", "i64", 1, "", "UserId")
val latency = schema_field_with_constraints(schema_field_optional("latency_ms", "i64", 2, "0", "ms", ""), "0", "1000", "")
val contract = SchemaContractModel.new("UserEvent", "1", [id, latency])

expect(contract.field_count()).to_equal(2)
expect(contract.required_names()).to_equal(["id"])
expect(contract.has_field("latency_ms")).to_equal(true)
expect(latency.is_optional()).to_equal(true)
expect(latency.default_value).to_equal("0")
expect(latency.unit_name).to_equal("ms")
expect(latency.min_value).to_equal("0")
expect(latency.max_value).to_equal("1000")
expect(id.identity).to_equal("UserId")
expect(id.field_id).to_equal(1)
```

</details>

#### exports JSON Schema 2020-12 compatible object metadata

- exports JSON Schema 2020-12 compatible object metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports JSON Schema 2020-12 compatible object metadata")
val id = schema_field_required("id", "i64", 1, "", "UserId")
val name = schema_field_with_constraints(schema_field_optional("name", "text", 2, "unknown", "", ""), "", "", "^[a-z]+$")
val contract = SchemaContractModel.new("User", "1", [id, name])

val exported = schema_contract_to_json_schema(contract)

expect(exported).to_contain("\"$schema\":\"https://json-schema.org/draft/2020-12/schema\"")
expect(exported).to_contain("\"title\":\"User\"")
expect(exported).to_contain("\"id\":{\"type\":\"integer\"")
expect(exported).to_contain("\"name\":{\"type\":\"string\"")
expect(exported).to_contain("\"default\":\"unknown\"")
expect(exported).to_contain("\"pattern\":\"^[a-z]+$\"")
expect(exported).to_contain("\"required\":[\"id\"]")
```

</details>

#### rejects unsafe protobuf-style field-number reuse

- rejects unsafe protobuf-style field-number reuse
   - Expected: compat.compatible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsafe protobuf-style field-number reuse")
val old_contract = SchemaContractModel.new("User", "1", [
    schema_field_required("id", "i64", 1, "", "UserId")
])
val renamed = SchemaContractModel.new("User", "2", [
    schema_field_required("account_id", "i64", 1, "", "UserId")
])

val compat = schema_contract_check_compat(old_contract, renamed)

expect(compat.compatible).to_equal(false)
expect(compat.error_0).to_contain("field id 1 reused")
```

</details>

#### rejects duplicate new field ids and emits canonical serialization

- rejects duplicate new field ids and emits canonical serialization
   - Expected: compat.compatible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects duplicate new field ids and emits canonical serialization")
val contract = SchemaContractModel.new("User", "2", [
    schema_field_required("id", "i64", 1, "", "UserId"),
    schema_field_optional("alias", "text", 1, "", "", "")
])
val compat = schema_contract_check_compat(SchemaContractModel.new("User", "1", []), contract)
val canonical = schema_contract_canonical(contract)

expect(compat.compatible).to_equal(false)
expect(compat.error_0).to_contain("duplicate field id 1")
expect(canonical).to_contain("User@2|")
expect(canonical).to_contain("1:id:i64")
```

</details>

#### lets SQP and API schemas reference the same contract definition

- lets SQP and API schemas reference the same contract definition
   - Expected: api_ref.consumer_kind equals `api`
   - Expected: sqp_ref.consumer_kind equals `sqp`
   - Expected: schema_reference_matches(api_ref, contract) is true
   - Expected: schema_reference_matches(sqp_ref, contract) is true
   - Expected: api_ref.contract_name equals `sqp_ref.contract_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lets SQP and API schemas reference the same contract definition")
val contract = SchemaContractModel.new("TelemetryEvent", "3", [
    schema_field_required("id", "i64", 1, "", "EventId")
])
val api_ref = schema_reference_for_api(contract)
val sqp_ref = schema_reference_for_sqp(contract)

expect(api_ref.consumer_kind).to_equal("api")
expect(sqp_ref.consumer_kind).to_equal("sqp")
expect(schema_reference_matches(api_ref, contract)).to_equal(true)
expect(schema_reference_matches(sqp_ref, contract)).to_equal(true)
expect(api_ref.contract_name).to_equal(sqp_ref.contract_name)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/schema_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering schema contract domain model.
- schema contract domain model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9371df4fae68d2e52621f94d77d752649b1c5e02b5136c543d4f8b4592abe03f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9371df4fae68d2e52621f94d77d752649b1c5e02b5136c543d4f8b4592abe03f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9371df4fae68d2e52621f94d77d752649b1c5e02b5136c543d4f8b4592abe03f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/schema_contract_spec.spl
mirror: doc/06_spec/unit/compiler/schema_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/schema_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/schema_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/schema_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/schema_contract_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports required and optional fields with defaults, units, identities, and field ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/schema_contract_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports JSON Schema 2020-12 compatible object metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/schema_contract_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unsafe protobuf-style field-number reuse' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
