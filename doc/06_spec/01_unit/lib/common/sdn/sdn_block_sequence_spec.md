# Sdn Block Sequence Specification

> Tests covering SDN block sequence of mappings parses into an Array.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdn Block Sequence Specification

## Scenarios

### SDN block sequence of mappings parses into an Array

#### yields an Array of 3 under project.dependencies

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- yields an Array of 3 under project.dependencies
- parse the src/app/simple.sdn shape and count the items
   - Expected: deps.len() equals `3`
   - Expected: "parse failed: " + e equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("yields an Array of 3 under project.dependencies")
step("parse the src/app/simple.sdn shape and count the items")
match parse(THREE):
    case Ok(v):
        val deps = (v.get_path("project.dependencies") ?? SdnValue.Null).as_array() ?? []
        expect(deps.len()).to_equal(3)
    case Err(e):
        expect("parse failed: " + e).to_equal("Ok")
```

</details>

#### preserves EVERY declared dependency path in order

- preserves EVERY declared dependency path in order
- read all three project values by index — no entry may be dropped
   - Expected: a + "|" + b + "|" + c equals `../compiler|../lib|../../rust`
   - Expected: "parse failed: " + e equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves EVERY declared dependency path in order")
step("read all three project values by index — no entry may be dropped")
match parse(THREE):
    case Ok(v):
        val a = (v.get_path("project.dependencies.0.project") ?? SdnValue.Null).as_str() ?? "<none>"
        val b = (v.get_path("project.dependencies.1.project") ?? SdnValue.Null).as_str() ?? "<none>"
        val c = (v.get_path("project.dependencies.2.project") ?? SdnValue.Null).as_str() ?? "<none>"
        expect(a + "|" + b + "|" + c).to_equal("../compiler|../lib|../../rust")
    case Err(e):
        expect("parse failed: " + e).to_equal("Ok")
```

</details>

#### never creates a literal '- project' key

- never creates a literal '- project' key
- the dash is sequence syntax, not part of the key text
   - Expected: v.get_path("project.dependencies.- project") == None is true
   - Expected: "parse failed: " + e equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never creates a literal '- project' key")
step("the dash is sequence syntax, not part of the key text")
match parse(THREE):
    case Ok(v):
        expect(v.get_path("project.dependencies.- project") == None).to_equal(true)
    case Err(e):
        expect("parse failed: " + e).to_equal("Ok")
```

</details>

#### still works for a single-item sequence

- still works for a single-item sequence
- one item must be an Array of 1, not a bare mapping
   - Expected: deps.len() equals `1`
   - Expected: "parse failed: " + e equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still works for a single-item sequence")
step("one item must be an Array of 1, not a bare mapping")
match parse(ONE):
    case Ok(v):
        val deps = (v.get_path("project.dependencies") ?? SdnValue.Null).as_array() ?? []
        expect(deps.len()).to_equal(1)
    case Err(e):
        expect("parse failed: " + e).to_equal("Ok")
```

</details>

#### single-item sequence exposes its mapping value

- single-item sequence exposes its mapping value
- index 0 of a one-item sequence carries the mapping
   - Expected: (v.get_path("project.dependencies.0.project") ?? SdnValue.Null).as_str() ?? "<none>" equals `../lib`
   - Expected: "parse failed: " + e equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-item sequence exposes its mapping value")
step("index 0 of a one-item sequence carries the mapping")
match parse(ONE):
    case Ok(v):
        expect((v.get_path("project.dependencies.0.project") ?? SdnValue.Null).as_str() ?? "<none>").to_equal("../lib")
    case Err(e):
        expect("parse failed: " + e).to_equal("Ok")
```

</details>

#### returns to the parent mapping after the sequence ends

- returns to the parent mapping after the sequence ends
- a sibling key at the parent indent after the sequence still parses
   - Expected: (v.get_path("project.root") ?? SdnValue.Null).as_str() ?? "<none>" equals `.`
   - Expected: "parse failed: " + e equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns to the parent mapping after the sequence ends")
step("a sibling key at the parent indent after the sequence still parses")
match parse(AFTER):
    case Ok(v):
        expect((v.get_path("project.root") ?? SdnValue.Null).as_str() ?? "<none>").to_equal(".")
    case Err(e):
        expect("parse failed: " + e).to_equal("Ok")
```

</details>

#### leaves ordinary nested mappings unchanged

- leaves ordinary nested mappings unchanged
- regression guard: no dash means no sequence
   - Expected: (v.get_path("project.name") ?? SdnValue.Null).as_str() ?? "<none>" equals `simple-app`
   - Expected: "parse failed: " + e equals `Ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves ordinary nested mappings unchanged")
step("regression guard: no dash means no sequence")
match parse("project:\n  name: simple-app\n  version: 1.0.0-RC\n"):
    case Ok(v):
        expect((v.get_path("project.name") ?? SdnValue.Null).as_str() ?? "<none>").to_equal("simple-app")
    case Err(e):
        expect("parse failed: " + e).to_equal("Ok")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/sdn/sdn_block_sequence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SDN block sequence of mappings parses into an Array.
- SDN block sequence of mappings parses into an Array

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4a7d0b78b805c0352c95e60ea1b610ddcbdf26173dd5ea74b887ef2e1746f8e0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a7d0b78b805c0352c95e60ea1b610ddcbdf26173dd5ea74b887ef2e1746f8e0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a7d0b78b805c0352c95e60ea1b610ddcbdf26173dd5ea74b887ef2e1746f8e0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/sdn/sdn_block_sequence_spec.spl
mirror: doc/06_spec/01_unit/lib/common/sdn/sdn_block_sequence_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/sdn/sdn_block_sequence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/sdn/sdn_block_sequence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/sdn/sdn_block_sequence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/sdn/sdn_block_sequence_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'yields an Array of 3 under project.dependencies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/sdn/sdn_block_sequence_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves EVERY declared dependency path in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/sdn/sdn_block_sequence_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never creates a literal '- project' key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
