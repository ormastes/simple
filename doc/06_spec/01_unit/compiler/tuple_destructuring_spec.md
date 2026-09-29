# tuple_destructuring_spec

> Purpose: Prove that tuple destructuring in val/var declarations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# tuple_destructuring_spec

Purpose: Prove that tuple destructuring in val/var declarations.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/tuple_destructuring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that tuple destructuring in val/var declarations.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### tuple destructuring in val/var declarations

#### binds both elements of a 2-tuple with val

- binds both elements of a 2-tuple with val
- Verify: binds both elements of a 2-tuple with val
   - Expected: a equals `1`
   - Expected: b equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds both elements of a 2-tuple with val")
step("Verify: binds both elements of a 2-tuple with val")
# @req: REQ-COMP-TUPLE-DESTRUCTURING-IN-VAL-VAR-DECLARATI-001
val (a, b) = pair()
expect(a).to_equal(1)
expect(b).to_equal(2)
```

</details>

#### binds all three elements of a mixed (text, text, i64) 3-tuple

- binds all three elements of a mixed (text, text, i64) 3-tuple
- Verify: binds all three elements of a mixed (text, text, i64) 3-tuple
   - Expected: o equals `out`
   - Expected: e equals `err`
   - Expected: c equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds all three elements of a mixed (text, text, i64) 3-tuple")
step("Verify: binds all three elements of a mixed (text, text, i64) 3-tuple")
val (o, e, c) = triple()
expect(o).to_equal("out")
expect(e).to_equal("err")
expect(c).to_equal(7)
```

</details>

#### binds a 3-tuple through var as well as val

- binds a 3-tuple through var as well as val
- Verify: binds a 3-tuple through var as well as val
   - Expected: o equals `out`
   - Expected: c equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds a 3-tuple through var as well as val")
step("Verify: binds a 3-tuple through var as well as val")
var (o, e, c) = triple()
expect(o).to_equal("out")
expect(c).to_equal(7)
```

</details>

#### binds the named element when others are wildcards

- binds the named element when others are wildcards
- Verify: binds the named element when others are wildcards
   - Expected: c equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds the named element when others are wildcards")
step("Verify: binds the named element when others are wildcards")
val (_, _, c) = triple()
expect(c).to_equal(7)
```

</details>

#### binds inside a non-main function body

- binds inside a non-main function body
- Verify: binds inside a non-main function body
   - Expected: triple_in_helper() equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds inside a non-main function body")
step("Verify: binds inside a non-main function body")
expect(triple_in_helper()).to_equal(7)
```

</details>

#### binds a nested tuple pattern

- binds a nested tuple pattern
- Verify: binds a nested tuple pattern
   - Expected: a equals `1`
   - Expected: b equals `2`
   - Expected: c equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds a nested tuple pattern")
step("Verify: binds a nested tuple pattern")
# HIR lowering cannot lower this pattern; the default engine deopts to
# the interpreter and the result is still correct. Guards the result,
# not the engine path.
val ((a, b), c) = nested()
expect(a).to_equal(1)
expect(b).to_equal(2)
expect(c).to_equal(3)
```

</details>

#### a failed destructure does not corrupt later examples

- a failed destructure does not corrupt later examples
- Verify: a failed destructure does not corrupt later examples
   - Expected: a + b equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("a failed destructure does not corrupt later examples")
step("Verify: a failed destructure does not corrupt later examples")
# Pins the cross-`it` finding: no environment leak exists. The reported
# "leak" was call-graph attribution through a shared broken helper.
# See the bug doc, section "The cross-`it` leak".
val (a, b) = pair()
expect(a + b).to_equal(3)
```

</details>

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

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-TUPLE-DESTRUCTURING-IN-VAL-VAR-DECLARATI-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d84b5f78a08bac60d4ef6b3edda770377d91903f60a33e5166ef496a10df6c40`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d84b5f78a08bac60d4ef6b3edda770377d91903f60a33e5166ef496a10df6c40`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d84b5f78a08bac60d4ef6b3edda770377d91903f60a33e5166ef496a10df6c40`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/tuple_destructuring_spec.spl
mirror: doc/06_spec/01_unit/compiler/tuple_destructuring_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/tuple_destructuring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/tuple_destructuring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/tuple_destructuring_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/tuple_destructuring_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds both elements of a 2-tuple with val' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/tuple_destructuring_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds all three elements of a mixed (text, text, i64) 3-tuple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/tuple_destructuring_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds a 3-tuple through var as well as val' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
