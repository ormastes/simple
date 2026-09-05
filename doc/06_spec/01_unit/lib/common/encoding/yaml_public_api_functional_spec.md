# Yaml Public Api Functional Specification

> Tests covering std.common.encoding.yaml public API is functional.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Yaml Public Api Functional Specification

## Scenarios

### std.common.encoding.yaml public API is functional

#### tags a block mapping node as a mapping

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- tags a block mapping node as a mapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tags a block mapping node as a mapping")
val node = yaml_parse("name: Alice\nage: 30\n")
assert_equal(node.0, "mapping")
```

</details>

#### returns the block mapping entries

- returns the block mapping entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the block mapping entries")
val entries = yaml_parse_mapping("name: Alice\nage: 30\n")
assert_equal(entries.length(), 2)
```

</details>

#### reads scalar values by key

- reads scalar values by key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads scalar values by key")
val entries = yaml_parse_mapping("name: Alice\nage: 30\n")
assert_equal(yaml_get(entries, "name"), "Alice")
assert_equal(yaml_get(entries, "age"), "30")
```

</details>

#### reads sequence values by key

- reads sequence values by key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads sequence values by key")
val entries = yaml_parse_mapping("tags:\n  - a\n  - b\n  - c\n")
assert_equal(yaml_get_list(entries, "tags").length(), 3)
```

</details>

#### strips comment lines before parsing

- strips comment lines before parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips comment lines before parsing")
val entries = yaml_parse_mapping("# header\nname: Alice\n")
assert_equal(yaml_get(entries, "name"), "Alice")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/yaml_public_api_functional_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.common.encoding.yaml public API is functional.
- std.common.encoding.yaml public API is functional

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

- Canonical SPipe generation for source `472cbb45243a4a84330c5ac0539bd4fa6594fd50173aba595bd715310b177c2e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `472cbb45243a4a84330c5ac0539bd4fa6594fd50173aba595bd715310b177c2e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `472cbb45243a4a84330c5ac0539bd4fa6594fd50173aba595bd715310b177c2e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/yaml_public_api_functional_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/yaml_public_api_functional_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/yaml_public_api_functional_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/yaml_public_api_functional_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/yaml_public_api_functional_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tags a block mapping node as a mapping' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/yaml_public_api_functional_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the block mapping entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/yaml_public_api_functional_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads scalar values by key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
