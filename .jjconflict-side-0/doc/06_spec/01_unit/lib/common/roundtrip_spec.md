# Roundtrip Specification

> Tests covering SDN Round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Roundtrip Specification

## Scenarios

### SDN Round-trip

#### parse -> serialize -> parse

#### preserves primitives

- preserves primitives
   - Expected: int_v == nil is false
   - Expected: str_v == nil is false
   - Expected: bool_v == nil is false
   - Expected: null_v == nil is false
   - Expected: "re-parse should succeed" equals ``
   - Expected: "parse should succeed" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves primitives")
"""Parse primitives, render, re-parse and verify values match."""
val source = "int_val: 42\nfloat_val: 3.14\nstr_val: hello\nbool_val: true\nnull_val: null"
match parse(source):
    case Ok(original):
        val serialized = _render_doc(original)
        match parse(serialized):
            case Ok(reparsed):
                val int_v = reparsed.get("int_val")
                expect(int_v == nil).to_equal(false)
                val str_v = reparsed.get("str_val")
                expect(str_v == nil).to_equal(false)
                val bool_v = reparsed.get("bool_val")
                expect(bool_v == nil).to_equal(false)
                val null_v = reparsed.get("null_val")
                expect(null_v == nil).to_equal(false)
            case Err(e):
                expect("re-parse should succeed").to_equal("")
    case Err(e):
        expect("parse should succeed").to_equal("")
```

</details>

#### preserves inline dicts

- preserves inline dicts
   - Expected: point == nil is false
   - Expected: "re-parse should succeed" equals ``
   - Expected: "parse should succeed" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves inline dicts")
"""Inline dict round-trip preserves all keys."""
val source = "point = " + "{" + "xval: 10, yval: 20, zval: 30" + "}"
match parse(source):
    case Ok(original):
        val serialized = _render_doc(original)
        match parse(serialized):
            case Ok(reparsed):
                val point = reparsed.get("point")
                expect(point == nil).to_equal(false)
            case Err(e):
                expect("re-parse should succeed").to_equal("")
    case Err(e):
        expect("parse should succeed").to_equal("")
```

</details>

#### preserves inline arrays

- preserves inline arrays
   - Expected: items == nil is false
   - Expected: "re-parse should succeed" equals ``
   - Expected: "parse should succeed" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves inline arrays")
"""Inline array round-trip preserves length and values."""
val source = "items = [1, 2, 3, 4, 5]"
match parse(source):
    case Ok(original):
        val serialized = _render_doc(original)
        match parse(serialized):
            case Ok(reparsed):
                val items = reparsed.get("items")
                expect(items == nil).to_equal(false)
            case Err(e):
                expect("re-parse should succeed").to_equal("")
    case Err(e):
        expect("parse should succeed").to_equal("")
```

</details>

#### preserves block dicts

- preserves block dicts
   - Expected: server == nil is false
   - Expected: "re-parse should succeed" equals ``
   - Expected: "parse should succeed" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves block dicts")
"""Block dict round-trip preserves nested keys."""
val source = "server:\n    host: localhost\n    port: 8080"
match parse(source):
    case Ok(original):
        val serialized = _render_doc(original)
        match parse(serialized):
            case Ok(reparsed):
                val server = reparsed.get("server")
                expect(server == nil).to_equal(false)
            case Err(e):
                expect("re-parse should succeed").to_equal("")
    case Err(e):
        expect("parse should succeed").to_equal("")
```

</details>

#### preserves block arrays

- preserves block arrays
   - Expected: fruits == nil is false
   - Expected: "re-parse should succeed" equals ``
   - Expected: "parse should succeed" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves block arrays")
"""Block array round-trip preserves all elements."""
val source = "fruits:\n    apple\n    banana\n    cherry"
match parse(source):
    case Ok(original):
        val serialized = _render_doc(original)
        match parse(serialized):
            case Ok(reparsed):
                val fruits = reparsed.get("fruits")
                expect(fruits == nil).to_equal(false)
            case Err(e):
                expect("re-parse should succeed").to_equal("")
    case Err(e):
        expect("parse should succeed").to_equal("")
```

</details>

#### preserves nested structures

- preserves nested structures
   - Expected: server_host == nil is false
   - Expected: db_name == nil is false
   - Expected: "parse should succeed" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves nested structures")
"""Nested block dict preserves deep structure."""
val source = "config:\n    server:\n        host: localhost\n        port: 8080\n    database:\n        name: mydb\n        port: 5432"
match parse(source):
    case Ok(original):
        val server_host = original.get_path("config.server.host")
        expect(server_host == nil).to_equal(false)
        val db_name = original.get_path("config.database.name")
        expect(db_name == nil).to_equal(false)
    case Err(e):
        expect("parse should succeed").to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SDN Round-trip.
- SDN Round-trip

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

- Canonical SPipe generation for source `2c975486b81f301acd55e270dc7f6ee52db4ae94a406b5e6b1536f5f97e6984c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c975486b81f301acd55e270dc7f6ee52db4ae94a406b5e6b1536f5f97e6984c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c975486b81f301acd55e270dc7f6ee52db4ae94a406b5e6b1536f5f97e6984c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/roundtrip_spec.spl
mirror: doc/06_spec/01_unit/lib/common/roundtrip_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/roundtrip_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves primitives' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/roundtrip_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves inline dicts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/roundtrip_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves inline arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
