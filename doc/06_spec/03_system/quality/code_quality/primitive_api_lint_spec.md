# Primitive API Lint Spec — Text Scanner Exemptions

> Tests the text-scanner lint (`check_primitive_api`) after Team W adds: SAME bare primitive is not flagged.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Primitive API Lint Spec — Text Scanner Exemptions

Tests the text-scanner lint (`check_primitive_api`) after Team W adds: SAME bare primitive is not flagged.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-primitive-api-suppressions |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/primitive_api_lint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the text-scanner lint (`check_primitive_api`) after Team W adds:
- D-1: pure-math exemption — `pub fn` where every param and return type is the
  SAME bare primitive is not flagged.
- D-2: extern fn exemption — lines starting with `extern fn` are never flagged.
- AC-7: `primitive_api` level is `deny` in `build_default_levels()` after Phase 2.

These specs WILL FAIL until Team W lands the exemptions and Phase 2 promotes the
level to `deny`. The existing integration spec at
`test/integration/app/primitive_api_lint_spec.spl` covers the base case;
this file covers the NEW exemption cases only.

## Scenarios

### primitive_api lint — D-1 pure-math exemption

#### AC-D1: should NOT flag pub fn with all-same-primitive args and return (i64)

- AC-D1: should NOT flag pub fn with all-same-primitive args and return (i64)
   - Expected: count_primitive_api_fixes(source) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-D1: should NOT flag pub fn with all-same-primitive args and return (i64)")
# Arrange: pure-math function — same type everywhere
val source =
    "pub fn add(a: i64, b: i64) -> i64:\n" +
    "    return a + b\n"
# Act + Assert: after Team W exemption, count must be 0
expect(count_primitive_api_fixes(source)).to_equal(0)
```

</details>

#### AC-D1: should NOT flag pub fn with all-same-primitive args and return (f64)

- AC-D1: should NOT flag pub fn with all-same-primitive args and return (f64)
   - Expected: count_primitive_api_fixes(source) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-D1: should NOT flag pub fn with all-same-primitive args and return (f64)")
val source =
    "pub fn lerp(a: f64, b: f64, t: f64) -> f64:\n" +
    "    return a + (b - a) * t\n"
expect(count_primitive_api_fixes(source)).to_equal(0)
```

</details>

#### AC-D1: should NOT flag single-arg single-return same-primitive fn

- AC-D1: should NOT flag single-arg single-return same-primitive fn
   - Expected: count_primitive_api_fixes(source) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-D1: should NOT flag single-arg single-return same-primitive fn")
val source =
    "pub fn negate(x: i64) -> i64:\n" +
    "    return 0 - x\n"
expect(count_primitive_api_fixes(source)).to_equal(0)
```

</details>

#### AC-D1: should STILL flag pub fn with mixed primitive types (i64 param, i32 return)

- AC-D1: should STILL flag pub fn with mixed primitive types (i64 param, i32 return)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-D1: should STILL flag pub fn with mixed primitive types (i64 param, i32 return)")
# Mixed types are NOT exempt — this must still fire
val source =
    "pub fn truncate(value: i64) -> i32:\n" +
    "    return value as i32\n"
expect(count_primitive_api_fixes(source)).to_be_greater_than(0)
```

</details>

#### AC-D1: should STILL flag pub fn with only a primitive return type (no params)

- AC-D1: should STILL flag pub fn with only a primitive return type (no params)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-D1: should STILL flag pub fn with only a primitive return type (no params)")
val source =
    "pub fn get_count() -> i64:\n" +
    "    return 0\n"
expect(count_primitive_api_fixes(source)).to_be_greater_than(0)
```

</details>

### primitive_api lint — D-2 extern fn exemption

#### AC-D2: should NOT flag extern fn with primitive args

- AC-D2: should NOT flag extern fn with primitive args
   - Expected: count_primitive_api_fixes(source) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-D2: should NOT flag extern fn with primitive args")
val source =
    "extern fn rt_alloc(size: i64) -> i64\n"
expect(count_primitive_api_fixes(source)).to_equal(0)
```

</details>

#### AC-D2: should NOT flag extern fn with mixed primitive types

- AC-D2: should NOT flag extern fn with mixed primitive types
   - Expected: count_primitive_api_fixes(source) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-D2: should NOT flag extern fn with mixed primitive types")
val source =
    "extern fn rt_read(fd: i32, buf: i64, len: i64) -> i32\n"
expect(count_primitive_api_fixes(source)).to_equal(0)
```

</details>

#### AC-D2: should STILL flag a regular pub fn that mirrors an extern signature

- AC-D2: should STILL flag a regular pub fn that mirrors an extern signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-D2: should STILL flag a regular pub fn that mirrors an extern signature")
# Same shape as extern, but declared pub fn — must still fire
val source =
    "pub fn wrap_alloc(size: i64) -> i32:\n" +
    "    return rt_alloc(size)\n"
expect(count_primitive_api_fixes(source)).to_be_greater_than(0)
```

</details>

### primitive_api lint — AC-7 deny level

#### AC-7: build_default_levels returns deny for primitive_api

- AC-7: build_default_levels returns deny for primitive_api
   - Expected: source contains `levels["primitive_api"] = "deny"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: build_default_levels returns deny for primitive_api")
val source = rt_file_read_text("src/compiler/90.tools/lint/_LintMain/config_and_model.spl")
expect(source.contains("levels[\"primitive_api\"] = \"deny\"")).to_equal(true)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4a5172750aeaac29fd292d08500917a83f3feee2586291adf59e0803a6537920`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4a5172750aeaac29fd292d08500917a83f3feee2586291adf59e0803a6537920`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4a5172750aeaac29fd292d08500917a83f3feee2586291adf59e0803a6537920`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/quality/code_quality/primitive_api_lint_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/primitive_api_lint_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/03_system/quality/code_quality/primitive_api_lint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/primitive_api_lint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/primitive_api_lint_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/quality/code_quality/primitive_api_lint_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/quality/code_quality/primitive_api_lint_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-D1: should NOT flag pub fn with all-same-primitive args and return (i64)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/primitive_api_lint_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-D1: should NOT flag pub fn with all-same-primitive args and return (f64)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/primitive_api_lint_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-D1: should NOT flag single-arg single-return same-primitive fn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
