# Yaml Flow Guard Specification

> Tests covering YAML flow collection guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Yaml Flow Guard Specification

## Scenarios

### YAML flow collection guards

#### keeps valid flow collections

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps valid flow collections


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid flow collections")
assert_equal(is_yaml_sequence(yaml_parse("[a, b]")), true)
assert_equal(is_yaml_mapping(yaml_parse("{name: Alice}")), true)
```

</details>

#### rejects unterminated flow collections through public parse

- rejects unterminated flow collections through public parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unterminated flow collections through public parse")
assert_equal(is_yaml_null(yaml_parse("[a, b")), true)
assert_equal(is_yaml_null(yaml_parse("{name: Alice")), true)
```

</details>

#### rejects unterminated flow collections through direct parsers

- rejects unterminated flow collections through direct parsers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unterminated flow collections through direct parsers")
assert_equal(is_yaml_null(yaml_parse_flow_sequence("[a, b")), true)
assert_equal(is_yaml_null(yaml_parse_flow_mapping("{name: Alice")), true)
```

</details>

#### does not expose malformed flow mappings as entries

- does not expose malformed flow mappings as entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not expose malformed flow mappings as entries")
val entries = yaml_parse_mapping("{name: Alice")
assert_equal(entries.length(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/yaml_flow_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering YAML flow collection guards.
- YAML flow collection guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `e5b7f4ff8d80d5abf34812077e2976b101a6a7c3e70f3331e6a0b31d502f3846`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5b7f4ff8d80d5abf34812077e2976b101a6a7c3e70f3331e6a0b31d502f3846`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5b7f4ff8d80d5abf34812077e2976b101a6a7c3e70f3331e6a0b31d502f3846`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/yaml_flow_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/yaml_flow_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/yaml_flow_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/yaml_flow_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/yaml_flow_guard_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid flow collections' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/yaml_flow_guard_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unterminated flow collections through public parse' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/yaml_flow_guard_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unterminated flow collections through direct parsers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
