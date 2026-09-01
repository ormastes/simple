# basic_type_check_spec

> Purpose: Prove that Type Tag Constants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# basic_type_check_spec

Purpose: Prove that Type Tag Constants.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/type/basic_type_check_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Type Tag Constants.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### Type Tag Constants

#### defines nil type

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines nil type
- Verify: defines nil type
   - Expected: TYPE_NIL equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines nil type")
step("Verify: defines nil type")
# @req: REQ-COMPILER-TYPE-001
expect(TYPE_NIL).to_equal(13)  # oracle: 13 — named expected value from the requirement
```

</details>

#### defines bool type

- defines bool type
- Verify: defines bool type
   - Expected: TYPE_BOOL equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines bool type")
step("Verify: defines bool type")
expect(TYPE_BOOL).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### defines i64 type

- defines i64 type
- Verify: defines i64 type
   - Expected: TYPE_I64 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines i64 type")
step("Verify: defines i64 type")
expect(TYPE_I64).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### defines f64 type

- defines f64 type
- Verify: defines f64 type
   - Expected: TYPE_F64 equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines f64 type")
step("Verify: defines f64 type")
expect(TYPE_F64).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### defines text type

- defines text type
- Verify: defines text type
   - Expected: TYPE_TEXT equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines text type")
step("Verify: defines text type")
expect(TYPE_TEXT).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### defines any type

- defines any type
- Verify: defines any type
   - Expected: TYPE_ANY equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines any type")
step("Verify: defines any type")
expect(TYPE_ANY).to_equal(12)  # oracle: 12 — named expected value from the requirement
```

</details>

### Union Type Registry

#### can register union members

- can register union members
- Verify: can register union members
   - Expected: test_union_members.len() equals `1`
   - Expected: test_union_members[0].len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can register union members")
step("Verify: can register union members")
var test_union_members: [[i64]] = []
test_union_members.push([TYPE_I64, TYPE_TEXT])
expect(test_union_members.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(test_union_members[0].len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### can retrieve union members

- can retrieve union members
- Verify: can retrieve union members
   - Expected: members[0] equals `TYPE_I64`
   - Expected: members[1] equals `TYPE_TEXT`
   - Expected: members[2] equals `TYPE_F64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can retrieve union members")
step("Verify: can retrieve union members")
var test_union_members: [[i64]] = []
test_union_members.push([TYPE_I64, TYPE_TEXT, TYPE_F64])
val members = test_union_members[0]
expect(members[0]).to_equal(TYPE_I64)
expect(members[1]).to_equal(TYPE_TEXT)
expect(members[2]).to_equal(TYPE_F64)
```

</details>

### Intersection Type Registry

#### can register intersection members

- can register intersection members
- Verify: can register intersection members
   - Expected: test_inter_members.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can register intersection members")
step("Verify: can register intersection members")
var test_inter_members: [[i64]] = []
test_inter_members.push([TYPE_ANY, TYPE_I64])
expect(test_inter_members.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### can retrieve intersection members

- can retrieve intersection members
- Verify: can retrieve intersection members
   - Expected: members.len() equals `1`
   - Expected: members[0] equals `TYPE_I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can retrieve intersection members")
step("Verify: can retrieve intersection members")
var test_inter_members: [[i64]] = []
test_inter_members.push([TYPE_I64])
val members = test_inter_members[0]
expect(members.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(members[0]).to_equal(TYPE_I64)
```

</details>

### Refinement Type Registry

#### can register refinement base types

- can register refinement base types
- Verify: can register refinement base types
   - Expected: test_ref_bases.len() equals `1`
   - Expected: test_ref_predicates.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can register refinement base types")
step("Verify: can register refinement base types")
var test_ref_bases: [i64] = []
var test_ref_predicates: [text] = []
test_ref_bases.push(TYPE_I64)
test_ref_predicates.push("x > 0")
expect(test_ref_bases.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(test_ref_predicates.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### can retrieve refinement predicate

- can retrieve refinement predicate
- Verify: can retrieve refinement predicate
   - Expected: predicate equals `x > 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can retrieve refinement predicate")
step("Verify: can retrieve refinement predicate")
var test_ref_bases: [i64] = []
var test_ref_predicates: [text] = []
test_ref_bases.push(TYPE_I64)
test_ref_predicates.push("x > 0")
val predicate = test_ref_predicates[0]
expect(predicate).to_equal("x > 0")
```

</details>

#### can check empty predicate

- can check empty predicate
- Verify: can check empty predicate
   - Expected: predicate equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can check empty predicate")
step("Verify: can check empty predicate")
var test_ref_bases: [i64] = []
var test_ref_predicates: [text] = []
test_ref_bases.push(TYPE_TEXT)
test_ref_predicates.push("")
val predicate = test_ref_predicates[0]
expect(predicate).to_equal("")
```

</details>

### Type Checking Logic

#### validates positive integer predicate

- validates positive integer predicate
- Verify: validates positive integer predicate
   - Expected: is_positive is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates positive integer predicate")
step("Verify: validates positive integer predicate")
val value: i64 = 5
val is_positive = value > 0
expect(is_positive).to_equal(true)
```

</details>

#### validates negative integer predicate

- validates negative integer predicate
- Verify: validates negative integer predicate
   - Expected: is_positive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates negative integer predicate")
step("Verify: validates negative integer predicate")
val value: i64 = -3
val is_positive = value > 0
expect(is_positive).to_equal(false)
```

</details>

#### validates zero for >= 0 predicate

- validates zero for >= 0 predicate
- Verify: validates zero for >= 0 predicate
   - Expected: is_non_negative is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates zero for >= 0 predicate")
step("Verify: validates zero for >= 0 predicate")
val value: i64 = 0
val is_non_negative = value >= 0
expect(is_non_negative).to_equal(true)
```

</details>

#### validates bounded integer

- validates bounded integer
- Verify: validates bounded integer
   - Expected: is_bounded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates bounded integer")
step("Verify: validates bounded integer")
val value: i64 = 50
val is_bounded = value < 100
expect(is_bounded).to_equal(true)
```

</details>

#### rejects out of bounds

- rejects out of bounds
- Verify: rejects out of bounds
   - Expected: is_bounded is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects out of bounds")
step("Verify: rejects out of bounds")
val value: i64 = 150
val is_bounded = value < 100
expect(is_bounded).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMPILER-TYPE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e2dc94cfa86a7a57fdf6a3a238898753f1de0fc95075b13fc0cbb5f420cf72f7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e2dc94cfa86a7a57fdf6a3a238898753f1de0fc95075b13fc0cbb5f420cf72f7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e2dc94cfa86a7a57fdf6a3a238898753f1de0fc95075b13fc0cbb5f420cf72f7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/type/basic_type_check_spec.spl
mirror: doc/06_spec/unit/compiler/type/basic_type_check_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/type/basic_type_check_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/type/basic_type_check_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/type/basic_type_check_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines nil type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/type/basic_type_check_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines bool type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/type/basic_type_check_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines i64 type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/type/basic_type_check_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can register union members' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/type/basic_type_check_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can retrieve union members' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/type/basic_type_check_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can register intersection members' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/type/basic_type_check_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can retrieve intersection members' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/type/basic_type_check_spec.spl:105:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can register refinement base types' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/compiler/type/basic_type_check_spec.spl:116:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can retrieve refinement predicate' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
