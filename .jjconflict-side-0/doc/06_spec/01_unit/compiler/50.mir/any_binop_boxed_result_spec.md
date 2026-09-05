# any_binop_boxed_result_spec

> Purpose: Prove that MIR any-operand binop boxing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# any_binop_boxed_result_spec

Purpose: Prove that MIR any-operand binop boxing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that MIR any-operand binop boxing.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### MIR any-operand binop boxing

#### should shift an any element correctly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should shift an any element correctly
- Verify: should shift an any element correctly
   - Expected: shr24(dst) equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should shift an any element correctly")
step("Verify: should shift an any element correctly")
# @req: REQ-COMP-MIR-ANY-OPERAND-BINOP-BOXING-001
var dst: [u32] = [1344853885]
expect(shr24(dst)).to_equal(80)
```

</details>

#### should mask an any element correctly

- should mask an any element correctly
- Verify: should mask an any element correctly
   - Expected: and_ff(dst) equals `125`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should mask an any element correctly")
step("Verify: should mask an any element correctly")
var dst: [u32] = [1344853885]
expect(and_ff(dst)).to_equal(125)
```

</details>

#### should chain shift-then-mask on an any element

- should chain shift-then-mask on an any element
- Verify: should chain shift-then-mask on an any element
   - Expected: nested(dst) equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should chain shift-then-mask on an any element")
step("Verify: should chain shift-then-mask on an any element")
var dst: [u32] = [1344853885]
expect(nested(dst)).to_equal(80)
```

</details>

#### should bit-or an any element correctly

- should bit-or an any element correctly
- Verify: should bit-or an any element correctly
   - Expected: or_zero(dst) equals `1344853885`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should bit-or an any element correctly")
step("Verify: should bit-or an any element correctly")
var dst: [u32] = [1344853885]
expect(or_zero(dst)).to_equal(1344853885)
```

</details>

#### should bit-xor an any element correctly

- should bit-xor an any element correctly
- Verify: should bit-xor an any element correctly
   - Expected: xor_zero(dst) equals `1344853885`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should bit-xor an any element correctly")
step("Verify: should bit-xor an any element correctly")
var dst: [u32] = [1344853885]
expect(xor_zero(dst)).to_equal(1344853885)
```

</details>

#### should subtract from an any element correctly

- should subtract from an any element correctly
- Verify: should subtract from an any element correctly
   - Expected: sub_base(dst) equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should subtract from an any element correctly")
step("Verify: should subtract from an any element correctly")
var dst: [u32] = [1344853885]
expect(sub_base(dst)).to_equal(80)
```

</details>

#### should multiply a masked any element correctly

- should multiply a masked any element correctly
- Verify: should multiply a masked any element correctly
   - Expected: mul_masked(dst) equals `250`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should multiply a masked any element correctly")
step("Verify: should multiply a masked any element correctly")
var dst: [u32] = [1344853885]
expect(mul_masked(dst)).to_equal(250)
```

</details>

#### should subtract float any elements correctly

- should subtract float any elements correctly
- Verify: should subtract float any elements correctly
   - Expected: fsub(dst) equals `5.25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should subtract float any elements correctly")
step("Verify: should subtract float any elements correctly")
var dst: [f64] = [7.75, 2.5]
expect(fsub(dst)).to_equal(5.25)
```

</details>

#### should multiply float any elements correctly

- should multiply float any elements correctly
- Verify: should multiply float any elements correctly
   - Expected: fmul(dst) equals `19.375`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should multiply float any elements correctly")
step("Verify: should multiply float any elements correctly")
var dst: [f64] = [7.75, 2.5]
expect(fmul(dst)).to_equal(19.375)
```

</details>

#### should divide float any elements correctly

- should divide float any elements correctly
- Verify: should divide float any elements correctly
   - Expected: fdiv(dst) equals `3.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should divide float any elements correctly")
step("Verify: should divide float any elements correctly")
var dst: [f64] = [7.75, 2.5]
expect(fdiv(dst)).to_equal(3.1)
```

</details>

#### should compare float any elements correctly

- should compare float any elements correctly
- Verify: should compare float any elements correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should compare float any elements correctly")
step("Verify: should compare float any elements correctly")
var dst: [f64] = [7.75, 2.5]
assert_false(flt(dst))
assert_true(fgt(dst))
```

</details>

#### should chain float any-element arithmetic correctly

- should chain float any-element arithmetic correctly
- Verify: should chain float any-element arithmetic correctly
   - Expected: fchain(dst) equals `10.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should chain float any-element arithmetic correctly")
step("Verify: should chain float any-element arithmetic correctly")
var dst: [f64] = [7.75, 2.5]
expect(fchain(dst)).to_equal(10.5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-MIR-ANY-OPERAND-BINOP-BOXING-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0f3665a37280ed40b790a8cda50fcc5e3927477ba95cb65fd6d5463b4e5e8428`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0f3665a37280ed40b790a8cda50fcc5e3927477ba95cb65fd6d5463b4e5e8428`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0f3665a37280ed40b790a8cda50fcc5e3927477ba95cb65fd6d5463b4e5e8428`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/any_binop_boxed_result_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/any_binop_boxed_result_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/any_binop_boxed_result_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should shift an any element correctly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should shift an any element correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl:96:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should mask an any element correctly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should mask an any element correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should chain shift-then-mask on an any element' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should chain shift-then-mask on an any element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl:110:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bit-or an any element correctly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl:117:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bit-xor an any element correctly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/any_binop_boxed_result_spec.spl:124:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should subtract from an any element correctly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
