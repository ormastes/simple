# spec_nullable_matcher_spec

> Regression: `expect(<T?>)` matchers must use nullable-aware equality.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spec_nullable_matcher_spec

Regression: `expect(<T?>)` matchers must use nullable-aware equality.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression: `expect(<T?>)` matchers must use nullable-aware equality.

A nullable `T?` has two runtime representations. A literal assigned to a `T?`
stays a bare value, but a function declared `-> T?` returns `Option::None` /
`Option::Some(x)`. The BDD matcher builtins used raw equality, so on a
function-returned nullable:

  - `to_equal(nil)` on a genuinely-nil value reported a FALSE FAILURE
  - `to_equal(x)`   on a genuinely-equal value reported a FALSE FAILURE
  - `to_not_equal(nil)` on a genuinely-nil value reported a FALSE PASS
  - `to_not_equal(x)`   on a genuinely-equal value reported a FALSE PASS

The false-pass direction is the dangerous one: ~26 `to_not_equal(nil)` sites
across kernel/loader/backend specs were asserting "this is not nil" and passing
unconditionally. Fixed by routing both matcher arms and the interpreter's
`==`/`!=` through `Value::nullable_eq` / `unwrap_option_payload`.

## Scenarios

### nullable-aware expect matchers

### to_equal must not FALSE-FAIL on a nullable receiver

#### matches nil against a function-returned nil i64?
#### matches nil against a function-returned nil text?

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nil_text()).to_equal(nil)
```

</details>

#### matches the payload of a function-returned i64?

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(some_i64()).to_equal(7)
```

</details>

#### matches the payload of a function-returned text?

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(some_text()).to_equal("hi")
```

</details>

### to_equal must still reject genuine mismatches

#### rejects nil for a non-nil nullable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(some_i64() == nil).to_be_false()
```

</details>

#### rejects a wrong payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(some_i64() == 8).to_be_false()
```

</details>

#### rejects a non-nil value for a nil nullable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nil_i64() == 7).to_be_false()
```

</details>

### to_not_equal must not FALSE-PASS on a nullable receiver

#### treats a function-returned nil as equal to nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nil_i64() == nil).to_be_true()
```

</details>

#### treats a function-returned payload as equal to the bare value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(some_i64() == 7).to_be_true()
```

</details>

#### still reports a genuine difference

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(some_i64()).to_not_equal(9)
```

</details>

#### still reports non-nil as not equal to nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(some_i64()).to_not_equal(nil)
```

</details>

### to_be_nil agrees with to_equal(nil)

#### passes for a function-returned nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nil_i64()).to_be_nil()
```

</details>

#### passes to_not_be_nil for a function-returned payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(some_i64()).to_not_be_nil()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `b8718080b539b4ac566abb882ee5d6d83278e1eb6b91910196603f135bb37adf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8718080b539b4ac566abb882ee5d6d83278e1eb6b91910196603f135bb37adf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8718080b539b4ac566abb882ee5d6d83278e1eb6b91910196603f135bb37adf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **81/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=90
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=81; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.spl:44:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'matches nil against a function-returned nil i64?' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.spl:49:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'matches nil against a function-returned nil text?' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.spl:52:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'matches the payload of a function-returned i64?' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.spl:55:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'matches the payload of a function-returned text?' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
