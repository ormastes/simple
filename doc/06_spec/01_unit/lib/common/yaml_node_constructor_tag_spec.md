# Yaml Node Constructor Tag Specification

> Tests covering yaml node constructors keep their tuple tag across the call boundary, yaml parsers forward the tuple tag intact.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Yaml Node Constructor Tag Specification

## Scenarios

### yaml node constructors keep their tuple tag across the call boundary

#### constructors expose .0 as the tag

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructors expose .0 as the tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructors expose .0 as the tag")
assert_equal(yaml_null().0, "null")
assert_equal(yaml_boolean(true).0, "boolean")
assert_equal(yaml_number("42").0, "number")
assert_equal(yaml_string("hi").0, "string")
assert_equal(yaml_sequence([]).0, "sequence")
assert_equal(yaml_mapping([]).0, "mapping")
```

</details>

#### tag predicates agree with the raw tag

- tag predicates agree with the raw tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tag predicates agree with the raw tag")
assert_equal(is_yaml_null(yaml_null()), true)
assert_equal(is_yaml_boolean(yaml_boolean(true)), true)
assert_equal(is_yaml_number(yaml_number("42")), true)
assert_equal(is_yaml_string(yaml_string("hi")), true)
assert_equal(is_yaml_sequence(yaml_sequence([])), true)
assert_equal(is_yaml_mapping(yaml_mapping([])), true)
```

</details>

### yaml parsers forward the tuple tag intact

#### scalar parsers tag their result

- scalar parsers tag their result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scalar parsers tag their result")
assert_equal(yaml_parse_scalar("42").0, "number")
assert_equal(yaml_parse_scalar("hi").0, "string")
```

</details>

#### flow parsers tag their result

- flow parsers tag their result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flow parsers tag their result")
assert_equal(yaml_parse_flow_sequence("[a, b]").0, "sequence")
assert_equal(yaml_parse_flow_mapping("{name: Alice}").0, "mapping")
```

</details>

#### block parser tags its result

- block parser tags its result


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("block parser tags its result")
assert_equal(yaml_parse_block("name: Alice\nage: 30").0, "mapping")
```

</details>

#### top-level parse tags its result

- top-level parse tags its result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("top-level parse tags its result")
assert_equal(yaml_parse("name: Alice\nage: 30").0, "mapping")
assert_equal(yaml_parse("[a, b]").0, "sequence")
assert_equal(yaml_parse("").0, "null")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/yaml_node_constructor_tag_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering yaml node constructors keep their tuple tag across the call boundary, yaml parsers forward the tuple tag intact.
- yaml node constructors keep their tuple tag across the call boundary
- yaml parsers forward the tuple tag intact

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `f4f62a2b17d88659d3515beff22fcdf41fa979af04e7715af9ca9daab9869ba2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f4f62a2b17d88659d3515beff22fcdf41fa979af04e7715af9ca9daab9869ba2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f4f62a2b17d88659d3515beff22fcdf41fa979af04e7715af9ca9daab9869ba2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/yaml_node_constructor_tag_spec.spl
mirror: doc/06_spec/01_unit/lib/common/yaml_node_constructor_tag_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/yaml_node_constructor_tag_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/yaml_node_constructor_tag_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/yaml_node_constructor_tag_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructors expose .0 as the tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/yaml_node_constructor_tag_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tag predicates agree with the raw tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/yaml_node_constructor_tag_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scalar parsers tag their result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
