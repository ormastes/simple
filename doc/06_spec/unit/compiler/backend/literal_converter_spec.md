# literal_converter_spec

> Purpose: Prove that LiteralConverter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# literal_converter_spec

Purpose: Prove that LiteralConverter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/literal_converter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that LiteralConverter.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### LiteralConverter

#### array conversion (STUB-003 fix)

#### returns Value.Array with all elements

- returns Value.Array with all elements
- Verify: returns Value.Array with all elements
   - Expected: elems.len() equals `3`
   - Expected: "not Array" equals `Array`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Value.Array with all elements")
step("Verify: returns Value.Array with all elements")
# @req: REQ-COMP-LITERALCONVERTER-001
val elements = [Value.Int(1), Value.Int(2), Value.Int(3)]
val result = LiteralConverter.convert_array(elements)
match result:
    case Value.Array(elems):
        expect(elems.len()).to_equal(3)
    case _:
        expect("not Array").to_equal("Array")
```

</details>

#### handles empty array

- handles empty array
- Verify: handles empty array
   - Expected: elems.len() equals `0`
   - Expected: "not Array" equals `Array`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty array")
step("Verify: handles empty array")
val result = LiteralConverter.convert_array([])
match result:
    case Value.Array(elems):
        expect(elems.len()).to_equal(0)
    case _:
        expect("not Array").to_equal("Array")
```

</details>

#### tuple conversion (STUB-003 fix)

#### returns Value.Tuple with all elements

- returns Value.Tuple with all elements
- Verify: returns Value.Tuple with all elements
   - Expected: elems.len() equals `2`
   - Expected: "not Tuple" equals `Tuple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Value.Tuple with all elements")
step("Verify: returns Value.Tuple with all elements")
val elements = [Value.String("a"), Value.Int(42)]
val result = LiteralConverter.convert_tuple(elements)
match result:
    case Value.Tuple(elems):
        expect(elems.len()).to_equal(2)
    case _:
        expect("not Tuple").to_equal("Tuple")
```

</details>

#### dict conversion (STUB-003 fix)

#### returns Value.Dict with string keys

- returns Value.Dict with string keys
- Verify: returns Value.Dict with string keys
   - Expected: entries.len() equals `2`
   - Expected: "not Dict" equals `Dict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Value.Dict with string keys")
step("Verify: returns Value.Dict with string keys")
val pairs = [(Value.String("x"), Value.Int(1)), (Value.String("y"), Value.Int(2))]
val result = LiteralConverter.convert_dict(pairs)
match result:
    case Value.Dict(entries):
        expect(entries.len()).to_equal(2)
    case _:
        expect("not Dict").to_equal("Dict")
```

</details>

#### handles empty dict

- handles empty dict
- Verify: handles empty dict
   - Expected: entries.len() equals `0`
   - Expected: "not Dict" equals `Dict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty dict")
step("Verify: handles empty dict")
val result = LiteralConverter.convert_dict([])
match result:
    case Value.Dict(entries):
        expect(entries.len()).to_equal(0)
    case _:
        expect("not Dict").to_equal("Dict")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMP-LITERALCONVERTER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5f92c87ec08bdeb60e70466383b0ecbc7686566baeb973aba6ce490f39220ef1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f92c87ec08bdeb60e70466383b0ecbc7686566baeb973aba6ce490f39220ef1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f92c87ec08bdeb60e70466383b0ecbc7686566baeb973aba6ce490f39220ef1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/backend/literal_converter_spec.spl
mirror: doc/06_spec/unit/compiler/backend/literal_converter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/literal_converter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/literal_converter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/literal_converter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/literal_converter_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Value.Array with all elements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/literal_converter_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/literal_converter_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Value.Tuple with all elements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
