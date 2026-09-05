# Optional-Returning Function Nil Truthiness Specification

> A function declared `-> T?` that yields nil must test FALSY under `if x:`,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optional-Returning Function Nil Truthiness Specification

A function declared `-> T?` that yields nil must test FALSY under `if x:`,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/interpreter/optional_return_nil_truthiness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

A function declared `-> T?` that yields nil must test FALSY under `if x:`,
exactly as a directly-bound nil does. Regression cover for
doc/08_tracking/bug/nil_optional_enum_return_truthy_2026-08-21.md, where nil
crossing an optional-typed function RETURN was coerced to an `Option::None`
enum value that landed in the interpreter's always-truthy arm — so `if x:`
took the then-branch for an absent value, silently and with no diagnostic.

The defect was interpreter-only (`SIMPLE_EXECUTION_MODE=interpreter`); the JIT
was already correct, which is why four earlier reduced fixtures all passed.
`bin/simple test` runs the tree-walk interpreter, so these examples exercise
the engine that was wrong.

## Scenarios

### optional-returning function nil truthiness

#### treats a nil returned from a T? function as falsy

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- treats a nil returned from a T? function as falsy
   - Expected: taken equals `else`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a nil returned from a T? function as falsy")
val k = absent_int()
var taken = "else"
if k:
    taken = "then"
expect(taken).to_equal("else")
```

</details>

#### treats an explicit `return nil` from a T? function as falsy

- treats an explicit `return nil` from a T? function as falsy
   - Expected: taken equals `else`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats an explicit `return nil` from a T? function as falsy")
val k = absent_via_return()
var taken = "else"
if k:
    taken = "then"
expect(taken).to_equal("else")
```

</details>

#### treats a nil-returning call tested inline as falsy

- treats a nil-returning call tested inline as falsy
   - Expected: taken equals `else`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a nil-returning call tested inline as falsy")
var taken = "else"
if absent_int():
    taken = "then"
expect(taken).to_equal("else")
```

</details>

#### treats a present value returned from a T? function as truthy

- treats a present value returned from a T? function as truthy
   - Expected: taken equals `then`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a present value returned from a T? function as truthy")
val k = present_int()
var taken = "else"
if k:
    taken = "then"
expect(taken).to_equal("then")
```

</details>

#### keeps `== nil` agreeing with the truthiness test

- keeps `== nil` agreeing with the truthiness test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps `== nil` agreeing with the truthiness test")
assert_true(absent_int() == nil)
assert_false(present_int() == nil)
```

</details>

#### keeps `.?` agreeing with the truthiness test

- keeps `.?` agreeing with the truthiness test


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps `.?` agreeing with the truthiness test")
assert_false(absent_int().?)
assert_true(present_int().?)
```

</details>

#### treats a nil optional-of-enum as falsy

- treats a nil optional-of-enum as falsy
   - Expected: taken equals `else`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a nil optional-of-enum as falsy")
# The originally reported shape: an enum-typed optional whose nil-ness
# decided whether a decorator contract was attached. Truthy here
# attached a @closed contract to an enum that never declared one.
val kind = absent_enum()
var taken = "else"
if kind:
    taken = "then"
expect(taken).to_equal("else")
```

</details>

#### treats a present payload-carrying enum variant as truthy

- treats a present payload-carrying enum variant as truthy
   - Expected: taken equals `then`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a present payload-carrying enum variant as truthy")
val kind = present_enum_payload()
var taken = "else"
if kind:
    taken = "then"
expect(taken).to_equal("then")
```

</details>

#### keeps a directly-bound nil falsy

- keeps a directly-bound nil falsy
   - Expected: taken equals `else`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a directly-bound nil falsy")
# This case was always correct (`Value::Nil` is falsy); it is asserted
# so a fix that regressed the direct binding cannot pass unnoticed.
val k: i64? = nil
var taken = "else"
if k:
    taken = "then"
expect(taken).to_equal("else")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `11a4d947065cb8587c41da776e9a98b963e3f56f52abb0fc6e2a338281dc83b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `11a4d947065cb8587c41da776e9a98b963e3f56f52abb0fc6e2a338281dc83b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `11a4d947065cb8587c41da776e9a98b963e3f56f52abb0fc6e2a338281dc83b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/interpreter/optional_return_nil_truthiness_spec.spl
mirror: doc/06_spec/unit/compiler/interpreter/optional_return_nil_truthiness_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/interpreter/optional_return_nil_truthiness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/interpreter/optional_return_nil_truthiness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/interpreter/optional_return_nil_truthiness_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a nil returned from a T? function as falsy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter/optional_return_nil_truthiness_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats an explicit `return nil` from a T? function as falsy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/interpreter/optional_return_nil_truthiness_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats a nil-returning call tested inline as falsy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
