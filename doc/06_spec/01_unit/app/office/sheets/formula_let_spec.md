# formula_let_spec

> Calc LET (and immediately-invoked LAMBDA) spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_let_spec

Calc LET (and immediately-invoked LAMBDA) spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_let_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc LET (and immediately-invoked LAMBDA) spec.

LET(name1, value1, [name2, value2, ...], calculation) binds names on a
module-level binding stack (see formula.spl's _let_names/_let_values next to
the CARD 14 _formula_origin_key precedent) that is pushed right before
evaluating anything that might reference a name and popped again before
_eval_let returns, on every path (success or #ERR) — so bindings never leak
across sibling LET calls or across cells. Ground truths below are hand
computed (LET is pure arithmetic/binding, not a numeric-library function, so
there is no external reference table to check against beyond direct
computation).

LAMBDA ships IMMEDIATE-INVOCATION ONLY: `LAMBDA(x, x*2)(3)` = 6. A LAMBDA
stored in a name via LET and invoked later (`LET(f, LAMBDA(x,x*2), f(3))`)
would need a callable CellValue variant plumbed through the whole engine —
out of scope; it fails closed with #ERR (see the "LAMBDA must be immediately
invoked" case below) rather than shipping half-working callable semantics.

## Scenarios

### Calc LET basic binding

#### LET(x, 5, x*2) = 10

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- LET(x, 5, x*2) = 10
   - Expected: _eval("=LET(x, 5, x*2)") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LET(x, 5, x*2) = 10")
expect(_eval("=LET(x, 5, x*2)")).to_equal("10")
```

</details>

#### LET(x, 5, y, x+1, x*y) = 30

- LET(x, 5, y, x+1, x*y) = 30
   - Expected: _eval("=LET(x, 5, y, x+1, x*y)") equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LET(x, 5, y, x+1, x*y) = 30")
expect(_eval("=LET(x, 5, y, x+1, x*y)")).to_equal("30")
```

</details>

#### value1 can reference a cell: LET(x, A1, x+1) with A1=10 -> 11

- value1 can reference a cell: LET(x, A1, x+1) with A1=10 -> 11
   - Expected: _eval_with_a1("=LET(x, A1, x+1)", "10") equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("value1 can reference a cell: LET(x, A1, x+1) with A1=10 -> 11")
expect(_eval_with_a1("=LET(x, A1, x+1)", "10")).to_equal("11")
```

</details>

#### a bound name can be used more than once in the calculation

- a bound name can be used more than once in the calculation
   - Expected: _eval("=LET(x, 3, x*x+x)") equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a bound name can be used more than once in the calculation")
expect(_eval("=LET(x, 3, x*x+x)")).to_equal("12")
```

</details>

#### value expressions may use string concatenation (full grammar, not just numeric)

- value expressions may use string concatenation (full grammar, not just numeric)
   - Expected: _eval("=LET(s, \"ab\"&\"c\", s)") equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("value expressions may use string concatenation (full grammar, not just numeric)")
expect(_eval("=LET(s, \"ab\"&\"c\", s)")).to_equal("abc")
```

</details>

### Calc LET scoping (no leakage, nesting, shadowing)

#### LET(x, 1, x) does not leak into a sibling LET(x, 2, x) in another cell

- LET(x, 1, x) does not leak into a sibling LET(x, 2, x) in another cell
   - Expected: _eval("=LET(x, 1, x)") equals `1`
   - Expected: _eval("=LET(x, 2, x)") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LET(x, 1, x) does not leak into a sibling LET(x, 2, x) in another cell")
expect(_eval("=LET(x, 1, x)")).to_equal("1")
expect(_eval("=LET(x, 2, x)")).to_equal("2")
```

</details>

#### nested LET(x,1,LET(y,2,x+y)) = 3 (outer name visible inside inner)

- nested LET(x,1,LET(y,2,x+y)) = 3 (outer name visible inside inner)
   - Expected: _eval("=LET(x,1,LET(y,2,x+y))") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested LET(x,1,LET(y,2,x+y)) = 3 (outer name visible inside inner)")
expect(_eval("=LET(x,1,LET(y,2,x+y))")).to_equal("3")
```

</details>

#### shadowing: LET(x,1,LET(x,5,x)) = 5 (innermost binding wins)

- shadowing: LET(x,1,LET(x,5,x)) = 5 (innermost binding wins)
   - Expected: _eval("=LET(x,1,LET(x,5,x))") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shadowing: LET(x,1,LET(x,5,x)) = 5 (innermost binding wins)")
expect(_eval("=LET(x,1,LET(x,5,x))")).to_equal("5")
```

</details>

#### after a nested LET returns, the outer binding is restored

- after a nested LET returns, the outer binding is restored
   - Expected: _eval("=LET(x,1,LET(x,5,x)) & \"-\" & LET(x,1,x)") equals `5-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("after a nested LET returns, the outer binding is restored")
expect(_eval("=LET(x,1,LET(x,5,x)) & \"-\" & LET(x,1,x)")).to_equal("5-1")
```

</details>

### Calc LET #ERR domains

#### a name matching a cell-ref pattern is rejected at bind time: LET(A1, 5, A1)

- a name matching a cell-ref pattern is rejected at bind time: LET(A1, 5, A1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a name matching a cell-ref pattern is rejected at bind time: LET(A1, 5, A1)")
expect(_eval("=LET(A1, 5, A1)")).to_contain("#ERR")
```

</details>

#### a name reusing a built-in function name is rejected: LET(SUM, 5, SUM)

- a name reusing a built-in function name is rejected: LET(SUM, 5, SUM)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a name reusing a built-in function name is rejected: LET(SUM, 5, SUM)")
expect(_eval("=LET(SUM, 5, SUM)")).to_contain("#ERR")
```

</details>

#### an even argument count (missing calculation) is #ERR: LET(x, 5)

- an even argument count (missing calculation) is #ERR: LET(x, 5)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an even argument count (missing calculation) is #ERR: LET(x, 5)")
expect(_eval("=LET(x, 5)")).to_contain("#ERR")
```

</details>

#### an even argument count (two pairs, no calculation) is #ERR: LET(x,5,y,6)

- an even argument count (two pairs, no calculation) is #ERR: LET(x,5,y,6)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an even argument count (two pairs, no calculation) is #ERR: LET(x,5,y,6)")
expect(_eval("=LET(x,5,y,6)")).to_contain("#ERR")
```

</details>

#### LET with no arguments is #ERR

- LET with no arguments is #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LET with no arguments is #ERR")
expect(_eval("=LET()")).to_contain("#ERR")
```

</details>

### Calc LAMBDA (immediate invocation only)

#### LAMBDA(x, x*2)(3) = 6

- LAMBDA(x, x*2)(3) = 6
   - Expected: _eval("=LAMBDA(x, x*2)(3)") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LAMBDA(x, x*2)(3) = 6")
expect(_eval("=LAMBDA(x, x*2)(3)")).to_equal("6")
```

</details>

#### LAMBDA(x, y, x+y)(2, 5) = 7 (multi-parameter)

- LAMBDA(x, y, x+y)(2, 5) = 7 (multi-parameter)
   - Expected: _eval("=LAMBDA(x, y, x+y)(2, 5)") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LAMBDA(x, y, x+y)(2, 5) = 7 (multi-parameter)")
expect(_eval("=LAMBDA(x, y, x+y)(2, 5)")).to_equal("7")
```

</details>

#### LAMBDA composes with LET's value expressions

- LAMBDA composes with LET's value expressions
   - Expected: _eval("=LET(f, LAMBDA(x, x*2)(3), f+1)") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LAMBDA composes with LET's value expressions")
expect(_eval("=LET(f, LAMBDA(x, x*2)(3), f+1)")).to_equal("7")
```

</details>

#### a LAMBDA not immediately invoked is unsupported and fails closed with #ERR

- a LAMBDA not immediately invoked is unsupported and fails closed with #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a LAMBDA not immediately invoked is unsupported and fails closed with #ERR")
expect(_eval("=LAMBDA(x, x*2)")).to_contain("#ERR")
```

</details>

#### LAMBDA arity mismatch (too few invocation arguments) is #ERR

- LAMBDA arity mismatch (too few invocation arguments) is #ERR


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LAMBDA arity mismatch (too few invocation arguments) is #ERR")
expect(_eval("=LAMBDA(x, y, x+y)(2)")).to_contain("#ERR")
```

</details>

### Calc LET deliberate-fail probe tail marker

#### tail of the file executes: LET(x, 5, x*2) still = 10

- tail of the file executes: LET(x, 5, x*2) still = 10
   - Expected: _eval("=LET(x, 5, x*2)") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tail of the file executes: LET(x, 5, x*2) still = 10")
expect(_eval("=LET(x, 5, x*2)")).to_equal("10")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `b24aa7a069da641400e2c37b81644bc291f16bd1384298dff3757b87959cd244`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b24aa7a069da641400e2c37b81644bc291f16bd1384298dff3757b87959cd244`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b24aa7a069da641400e2c37b81644bc291f16bd1384298dff3757b87959cd244`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_let_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_let_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_let_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_let_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_let_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LET(x, 5, x*2) = 10' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_let_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LET(x, 5, y, x+1, x*y) = 30' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_let_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'value1 can reference a cell: LET(x, A1, x+1) with A1=10 -> 11' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
