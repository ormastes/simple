# Schema Contract Specification

> <details>

<!-- sdn-diagram:id=schema_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=schema_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

schema_contract_spec -> std
schema_contract_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=schema_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Schema Contract Specification

## Scenarios

### schema contract domain model

#### supports required and optional fields with defaults, units, identities, and field ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. schema field required
2. schema field required
   - Expected: compat.compatible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. schema field required
2. schema field optional
   - Expected: compat.compatible is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. schema field required
   - Expected: api_ref.consumer_kind equals `api`
   - Expected: sqp_ref.consumer_kind equals `sqp`
   - Expected: schema_reference_matches(api_ref, contract) is true
   - Expected: schema_reference_matches(sqp_ref, contract) is true
   - Expected: api_ref.contract_name equals `sqp_ref.contract_name`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/compiler/schema_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
