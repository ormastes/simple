# Result Unwrap Payload Type Preserved Specification

> Tests covering Result<T, E>.unwrap() payload type on an unannotated local.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Result Unwrap Payload Type Preserved Specification

## Scenarios

### Result<T, E>.unwrap() payload type on an unannotated local

#### resolves the method against T, not a same-named method on another type

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves the method against T, not a same-named method on another type
   - Expected: module.emit_object() equals `111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("resolves the method against T, not a same-named method on another type")
val compiled = make_payload_a()
val module = compiled.unwrap()
expect(module.emit_object()).to_equal(111)
```

</details>

#### still dispatches the colliding same-named method on the other type

- still dispatches the colliding same-named method on the other type
   - Expected: other.emit_object() equals `205`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("still dispatches the colliding same-named method on the other type")
val other = UnwrapPayloadB(y: 5)
expect(other.emit_object()).to_equal(205)
```

</details>

#### agrees with the explicitly annotated receiver (the old workaround)

- agrees with the explicitly annotated receiver (the old workaround)
   - Expected: inferred.emit_object() equals `annotated.emit_object()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("agrees with the explicitly annotated receiver (the old workaround)")
val compiled = make_payload_a()
val annotated: UnwrapPayloadA = compiled.unwrap()
val inferred = make_payload_a().unwrap()
expect(inferred.emit_object()).to_equal(annotated.emit_object())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/result_unwrap_payload_type_preserved_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Result<T, E>.unwrap() payload type on an unannotated local.
- Result<T, E>.unwrap() payload type on an unannotated local

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LANGUAGE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2d38d8f445a2bf767e0aa11397cd4b0c37ee79787a7e1a7d55625d4b35e74e27`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2d38d8f445a2bf767e0aa11397cd4b0c37ee79787a7e1a7d55625d4b35e74e27`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2d38d8f445a2bf767e0aa11397cd4b0c37ee79787a7e1a7d55625d4b35e74e27`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/language/result_unwrap_payload_type_preserved_spec.spl
mirror: doc/06_spec/01_unit/language/result_unwrap_payload_type_preserved_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/result_unwrap_payload_type_preserved_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/result_unwrap_payload_type_preserved_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/result_unwrap_payload_type_preserved_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/language/result_unwrap_payload_type_preserved_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the method against T, not a same-named method on another type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/result_unwrap_payload_type_preserved_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still dispatches the colliding same-named method on the other type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/result_unwrap_payload_type_preserved_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees with the explicitly annotated receiver (the old workaround)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
