# Compound Assignment Resolves One Place (Load + Store)

> Purpose: Prove that compound assignment on a struct field (one hop).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compound Assignment Resolves One Place (Load + Store)

Purpose: Prove that compound assignment on a struct field (one hop).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/01_unit/compiler/compound_assign_place_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that compound assignment on a struct field (one hop).
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### compound assignment on a struct field (one hop)

#### adds to the field's current value, not to zero

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- adds to the field's current value, not to zero
- Verify: adds to the field's current value, not to zero
   - Expected: s.n equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("adds to the field's current value, not to zero")
step("Verify: adds to the field's current value, not to zero")
# @req: REQ-COMP-COMPOUND-ASSIGNMENT-ON-A-STRUCT-FIELD-ON-001
var s = CaCounter(n: 5)
s.n += 2
expect(s.n).to_equal(7)
```

</details>

#### accumulates across repeated compound adds

- accumulates across repeated compound adds
- Verify: accumulates across repeated compound adds
   - Expected: s.n equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accumulates across repeated compound adds")
step("Verify: accumulates across repeated compound adds")
var s = CaCounter(n: 0)
s.n += 4
s.n += 3
expect(s.n).to_equal(7)
```

</details>

#### subtracts from the field's current value

- subtracts from the field's current value
- Verify: subtracts from the field's current value
   - Expected: s.n equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("subtracts from the field's current value")
step("Verify: subtracts from the field's current value")
var s = CaCounter(n: 10)
s.n -= 4
expect(s.n).to_equal(6)
```

</details>

#### multiplies the field's current value

- multiplies the field's current value
- Verify: multiplies the field's current value
   - Expected: s.n equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("multiplies the field's current value")
step("Verify: multiplies the field's current value")
var s = CaCounter(n: 6)
s.n *= 7
expect(s.n).to_equal(42)
```

</details>

#### divides the field's current value

- divides the field's current value
- Verify: divides the field's current value
   - Expected: s.n equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("divides the field's current value")
step("Verify: divides the field's current value")
var s = CaCounter(n: 84)
s.n /= 4
expect(s.n).to_equal(21)
```

</details>

### compound assignment on a nested struct field (two and three hops)

#### two hops: mid.inner reads the current value

- two hops: mid.inner reads the current value
- Verify: two hops: mid.inner reads the current value
   - Expected: m.inner.n equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("two hops: mid.inner reads the current value")
step("Verify: two hops: mid.inner reads the current value")
var m = CaMid(inner: CaInner(n: 5))
m.inner.n += 2
expect(m.inner.n).to_equal(7)
```

</details>

#### three hops: outer.mid.inner accumulates from zero

- three hops: outer.mid.inner accumulates from zero
- Verify: three hops: outer.mid.inner accumulates from zero
   - Expected: c.mid.inner.n equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("three hops: outer.mid.inner accumulates from zero")
step("Verify: three hops: outer.mid.inner accumulates from zero")
var c = CaOuter(mid: CaMid(inner: CaInner(n: 0)))
c.mid.inner.n += 4
c.mid.inner.n += 3
expect(c.mid.inner.n).to_equal(7)
```

</details>

#### three hops: outer.mid.inner starting non-zero

- three hops: outer.mid.inner starting non-zero
- Verify: three hops: outer.mid.inner starting non-zero
   - Expected: c.mid.inner.n equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("three hops: outer.mid.inner starting non-zero")
step("Verify: three hops: outer.mid.inner starting non-zero")
var c = CaOuter(mid: CaMid(inner: CaInner(n: 5)))
c.mid.inner.n += 2
expect(c.mid.inner.n).to_equal(7)
```

</details>

### compound assignment on an array element

#### adds to the element's current value, not to zero

- adds to the element's current value, not to zero
- Verify: adds to the element's current value, not to zero
   - Expected: arr[1] equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("adds to the element's current value, not to zero")
step("Verify: adds to the element's current value, not to zero")
var arr = [1, 2, 3]
arr[1] += 10
expect(arr[1]).to_equal(12)
```

</details>

#### leaves the untouched elements alone

- leaves the untouched elements alone
- Verify: leaves the untouched elements alone
   - Expected: arr[0] equals `1`
   - Expected: arr[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves the untouched elements alone")
step("Verify: leaves the untouched elements alone")
var arr = [1, 2, 3]
arr[1] += 10
expect(arr[0]).to_equal(1)
expect(arr[2]).to_equal(3)
```

</details>

#### accumulates across repeated compound adds on one element

- accumulates across repeated compound adds on one element
- Verify: accumulates across repeated compound adds on one element
   - Expected: arr[2] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accumulates across repeated compound adds on one element")
step("Verify: accumulates across repeated compound adds on one element")
var arr = [0, 0, 0]
arr[2] += 4
arr[2] += 3
expect(arr[2]).to_equal(7)
```

</details>

#### subtracts from the element's current value

- subtracts from the element's current value
- Verify: subtracts from the element's current value
   - Expected: arr[0] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("subtracts from the element's current value")
step("Verify: subtracts from the element's current value")
var arr = [10, 20, 30]
arr[0] -= 4
expect(arr[0]).to_equal(6)
```

</details>

### compound assignment evaluates the place subexpression exactly once

#### does not double-apply the index when the index comes from a var

- does not double-apply the index when the index comes from a var
- Verify: does not double-apply the index when the index comes from a var
   - Expected: arr[0] equals `1`
   - Expected: arr[1] equals `12`
   - Expected: arr[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not double-apply the index when the index comes from a var")
step("Verify: does not double-apply the index when the index comes from a var")
# A lowering that resolved the place twice (once for the load, once
# for the store) would show up here as a write to the wrong slot.
var arr = [1, 2, 3]
var i = 1
arr[i] += 10
expect(arr[0]).to_equal(1)
expect(arr[1]).to_equal(12)
expect(arr[2]).to_equal(3)
```

</details>

### explicit read-modify-write control (never broken)

#### one hop: t.n = t.n + 2

- one hop: t.n = t.n + 2
- Verify: one hop: t.n = t.n + 2
   - Expected: t.n equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("one hop: t.n = t.n + 2")
step("Verify: one hop: t.n = t.n + 2")
var t = CaCounter(n: 5)
t.n = t.n + 2
expect(t.n).to_equal(7)
```

</details>

#### three hops: c.mid.inner.n = c.mid.inner.n + 2

- three hops: c.mid.inner.n = c.mid.inner.n + 2
- Verify: three hops: c.mid.inner.n = c.mid.inner.n + 2
   - Expected: c.mid.inner.n equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("three hops: c.mid.inner.n = c.mid.inner.n + 2")
step("Verify: three hops: c.mid.inner.n = c.mid.inner.n + 2")
var c = CaOuter(mid: CaMid(inner: CaInner(n: 5)))
c.mid.inner.n = c.mid.inner.n + 2
expect(c.mid.inner.n).to_equal(7)
```

</details>

#### array element: arr[1] = arr[1] + 10

- array element: arr[1] = arr[1] + 10
- Verify: array element: arr[1] = arr[1] + 10
   - Expected: arr[1] equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("array element: arr[1] = arr[1] + 10")
step("Verify: array element: arr[1] = arr[1] + 10")
var arr = [1, 2, 3]
arr[1] = arr[1] + 10
expect(arr[1]).to_equal(12)
```

</details>

#### local variable compound assign (the arm that already worked)

- local variable compound assign (the arm that already worked)
- Verify: local variable compound assign (the arm that already worked)
   - Expected: n equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("local variable compound assign (the arm that already worked)")
step("Verify: local variable compound assign (the arm that already worked)")
var n = 5
n += 2
expect(n).to_equal(7)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-COMPOUND-ASSIGNMENT-ON-A-STRUCT-FIELD-ON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3608de83e92daf1cc81027bdd5ae685f5978cff87795f790e9f71de3217fe4cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3608de83e92daf1cc81027bdd5ae685f5978cff87795f790e9f71de3217fe4cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3608de83e92daf1cc81027bdd5ae685f5978cff87795f790e9f71de3217fe4cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/compound_assign_place_spec.spl
mirror: doc/06_spec/01_unit/compiler/compound_assign_place_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/compound_assign_place_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/compound_assign_place_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/compound_assign_place_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/compound_assign_place_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds to the field's current value, not to zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/compound_assign_place_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accumulates across repeated compound adds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/compound_assign_place_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'subtracts from the field's current value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
