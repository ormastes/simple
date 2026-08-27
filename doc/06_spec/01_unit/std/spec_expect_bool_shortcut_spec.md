# spec_expect_bool_shortcut_spec

> Verifies concise boolean assertions:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spec_expect_bool_shortcut_spec

Verifies concise boolean assertions:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/spec_expect_bool_shortcut_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies concise boolean assertions:
    `expect(condition)` asserts true and `expect_not(condition)` asserts false.
    Matcher chains such as `expect(value).to_equal(value)` remain supported for
    non-boolean equality.

## Scenarios

### std.spec boolean expectation shortcuts

#### accepts bare expect for true boolean expressions

- accepts bare expect for true boolean expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("accepts bare expect for true boolean expressions")
assert_true(true)
val condition = 2 + 2 == 4
assert_true(condition)
check(condition)
check_msg(condition, "condition should be true")
```

</details>

#### accepts expect_not for false boolean expressions

- accepts expect_not for false boolean expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("accepts expect_not for false boolean expressions")
expect_not(false)
val condition = "abc".contains("z")
expect_not(condition)
expect_not(2 + 2 == 5)
```

</details>

#### keeps matcher equality for non-boolean values

- keeps matcher equality for non-boolean values
   - Expected: 42 equals `42`
   - Expected: "simple" equals `simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-STD
step("keeps matcher equality for non-boolean values")
expect(42).to_equal(42)
expect("simple").to_equal("simple")
```

</details>

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

- `REQ-SSPEC-STD`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e25e24ae7b52a450106dd85452e3d201623c901c6b525c19c1f5ca97fd452f58`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e25e24ae7b52a450106dd85452e3d201623c901c6b525c19c1f5ca97fd452f58`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e25e24ae7b52a450106dd85452e3d201623c901c6b525c19c1f5ca97fd452f58`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/std/spec_expect_bool_shortcut_spec.spl
mirror: doc/06_spec/01_unit/std/spec_expect_bool_shortcut_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/spec_expect_bool_shortcut_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/spec_expect_bool_shortcut_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/spec_expect_bool_shortcut_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/std/spec_expect_bool_shortcut_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts bare expect for true boolean expressions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/spec_expect_bool_shortcut_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts expect_not for false boolean expressions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/spec_expect_bool_shortcut_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps matcher equality for non-boolean values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
