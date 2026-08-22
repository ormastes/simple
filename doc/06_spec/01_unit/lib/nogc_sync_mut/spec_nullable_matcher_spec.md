# spec_nullable_matcher_spec

> stays a bare value, but a function declared `-> T?` returns `Option::None` /

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spec_nullable_matcher_spec

stays a bare value, but a function declared `-> T?` returns `Option::None` /

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

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

- Verify: matches nil against a function-returned nil i64?
   - Expected: nil_i64() equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: matches nil against a function-returned nil i64?")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(nil_i64()).to_equal(nil)
```

</details>

#### matches nil against a function-returned nil text?

- Verify: matches nil against a function-returned nil text?
   - Expected: nil_text() equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: matches nil against a function-returned nil text?")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(nil_text()).to_equal(nil)
```

</details>

#### matches the payload of a function-returned i64?

- Verify: matches the payload of a function-returned i64?
   - Expected: some_i64() equals `7)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: matches the payload of a function-returned i64?")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(some_i64()).to_equal(7)  # oracle: pinned constant asserted by this scenario
```

</details>

#### matches the payload of a function-returned text?

- Verify: matches the payload of a function-returned text?
   - Expected: some_text() equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: matches the payload of a function-returned text?")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(some_text()).to_equal("hi")
```

</details>

### to_equal must still reject genuine mismatches

#### rejects nil for a non-nil nullable

- Verify: rejects nil for a non-nil nullable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: rejects nil for a non-nil nullable")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(some_i64() == nil).to_be_false()
```

</details>

#### rejects a wrong payload

- Verify: rejects a wrong payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: rejects a wrong payload")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(some_i64() == 8).to_be_false()
```

</details>

#### rejects a non-nil value for a nil nullable

- Verify: rejects a non-nil value for a nil nullable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: rejects a non-nil value for a nil nullable")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(nil_i64() == 7).to_be_false()
```

</details>

### to_not_equal must not FALSE-PASS on a nullable receiver

#### treats a function-returned nil as equal to nil

- Verify: treats a function-returned nil as equal to nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: treats a function-returned nil as equal to nil")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(nil_i64() == nil).to_be_true()
```

</details>

#### treats a function-returned payload as equal to the bare value

- Verify: treats a function-returned payload as equal to the bare value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: treats a function-returned payload as equal to the bare value")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(some_i64() == 7).to_be_true()
```

</details>

#### still reports a genuine difference

- Verify: still reports a genuine difference


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: still reports a genuine difference")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(some_i64()).to_not_equal(9)
```

</details>

#### still reports non-nil as not equal to nil

- Verify: still reports non-nil as not equal to nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: still reports non-nil as not equal to nil")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(some_i64()).to_not_equal(nil)
```

</details>

### to_be_nil agrees with to_equal(nil)

#### passes for a function-returned nil

- Verify: passes for a function-returned nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: passes for a function-returned nil")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(nil_i64()).to_be_nil()
```

</details>

#### passes to_not_be_nil for a function-returned payload

- Verify: passes to_not_be_nil for a function-returned payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-NOGC_SYNC_MUT_SPEC_NULLABLE_-001
step("Verify: passes to_not_be_nil for a function-returned payload")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e49efd57518b6dacc36ae542327a9d13d91354cf0cc204603952df2e8b80e56`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e49efd57518b6dacc36ae542327a9d13d91354cf0cc204603952df2e8b80e56`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e49efd57518b6dacc36ae542327a9d13d91354cf0cc204603952df2e8b80e56`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/spec_nullable_matcher_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
