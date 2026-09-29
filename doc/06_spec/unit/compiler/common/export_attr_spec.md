# ExportAttr Parsing Specification

> Tests the `ExportAttr` struct and `parse_export_attrs()` function which parses `@export("C")` and `@export("C", name: "custom")` annotations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ExportAttr Parsing Specification

Tests the `ExportAttr` struct and `parse_export_attrs()` function which parses `@export("C")` and `@export("C", name: "custom")` annotations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFFI-EXPORT-001 |
| Category | Compiler / Attributes |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | SFFI bidirectional class interop |
| Plan | parsed-questing-goose.md |
| Design | sffi_external_library_pattern.md |
| Source | `test/unit/compiler/common/export_attr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the `ExportAttr` struct and `parse_export_attrs()` function which
parses `@export("C")` and `@export("C", name: "custom")` annotations.

## Key Concepts

| Concept | Description |
|---------|-------------|
| ExportAttr | Struct holding is_export_c and export_name |
| parse_export_attrs | Scans [Attribute] for @export("C") |
| Custom name | Optional name: kwarg for C symbol override |

## Scenarios

### ExportAttr

### parse_export_attrs

#### returns nil when no @export attribute

- returns nil when no @export attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil when no @export attribute")
val attrs: [Attribute] = [make_unrelated_attr()]
val result = parse_export_attrs(attrs)
expect(result).to_be_nil()
```

</details>

#### returns nil for empty attribute list

- returns nil for empty attribute list


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for empty attribute list")
val attrs: [Attribute] = []
val result = parse_export_attrs(attrs)
expect(result).to_be_nil()
```

</details>

#### parses @export('C') correctly

- parses @export('C') correctly
   - Expected: result != nil is true
   - Expected: ea.is_export_c is true
   - Expected: ea.export_name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses @export('C') correctly")
val attrs: [Attribute] = [make_export_c_attr()]
val result = parse_export_attrs(attrs)
expect(result != nil).to_equal(true)
val ea = result.unwrap()
expect(ea.is_export_c).to_equal(true)
expect(ea.export_name).to_equal("")
```

</details>

#### parses @export('C', name: 'custom') with custom name

- parses @export('C', name: 'custom') with custom name
   - Expected: result != nil is true
   - Expected: ea.is_export_c is true
   - Expected: ea.export_name equals `my_calc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses @export('C', name: 'custom') with custom name")
val attrs: [Attribute] = [make_export_c_named_attr("my_calc")]
val result = parse_export_attrs(attrs)
expect(result != nil).to_equal(true)
val ea = result.unwrap()
expect(ea.is_export_c).to_equal(true)
expect(ea.export_name).to_equal("my_calc")
```

</details>

#### returns nil for @export without arguments

- returns nil for @export without arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for @export without arguments")
val attrs: [Attribute] = [make_export_no_args_attr()]
val result = parse_export_attrs(attrs)
expect(result).to_be_nil()
```

</details>

#### returns nil for @export with non-C target

- returns nil for @export with non-C target


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for @export with non-C target")
val attrs: [Attribute] = [make_export_python_attr()]
val result = parse_export_attrs(attrs)
expect(result).to_be_nil()
```

</details>

#### finds @export among multiple attributes

- finds @export among multiple attributes
   - Expected: result != nil is true
   - Expected: ea.is_export_c is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds @export among multiple attributes")
val attrs: [Attribute] = [
    make_unrelated_attr(),
    make_export_c_attr(),
    make_unrelated_attr()
]
val result = parse_export_attrs(attrs)
expect(result != nil).to_equal(true)
val ea = result.unwrap()
expect(ea.is_export_c).to_equal(true)
```

</details>

### ExportAttr struct

#### can be constructed with default values

- can be constructed with default values
   - Expected: ea.is_export_c is false
   - Expected: ea.export_name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can be constructed with default values")
val ea = ExportAttr(is_export_c: false, export_name: "")
expect(ea.is_export_c).to_equal(false)
expect(ea.export_name).to_equal("")
```

</details>

#### can be constructed with export enabled

- can be constructed with export enabled
   - Expected: ea.is_export_c is true
   - Expected: ea.export_name equals `my_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can be constructed with export enabled")
val ea = ExportAttr(is_export_c: true, export_name: "my_fn")
expect(ea.is_export_c).to_equal(true)
expect(ea.export_name).to_equal("my_fn")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `SFFI bidirectional class interop`
- **Plan:** `parsed-questing-goose.md`
- **Design:** `sffi_external_library_pattern.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3bae2c8a07391fcb7c9525e7b2286089aa7e79cd2c666c97e551fb23b0b25b53`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3bae2c8a07391fcb7c9525e7b2286089aa7e79cd2c666c97e551fb23b0b25b53`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3bae2c8a07391fcb7c9525e7b2286089aa7e79cd2c666c97e551fb23b0b25b53`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/compiler/common/export_attr_spec.spl
mirror: doc/06_spec/unit/compiler/common/export_attr_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/common/export_attr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/common/export_attr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/common/export_attr_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil when no @export attribute' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/common/export_attr_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for empty attribute list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/common/export_attr_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses @export('C') correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/common/export_attr_spec.spl:187:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be constructed with default values' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/common/export_attr_spec.spl:194:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be constructed with export enabled' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
