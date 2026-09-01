# Lint Checks Specification

> Tests covering check_raw_rt_access, check_param_tag, check_module_init_literal.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lint Checks Specification

## Scenarios

### check_raw_rt_access

#### flags an extern rt_* declaration in non-privileged app code

- flags an extern rt_* declaration in non-privileged app code
   - Expected: findings.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags an extern rt_* declaration in non-privileged app code")
val source = "fn helper():\n    extern fn rt_frobnicate(x: i64) -> i64\n    0\n"
val findings = check_raw_rt_access(source, "src/app/cli/example.spl")
expect(findings.len() > 0).to_equal(true)
assert_equal(findings[0].code, "RAW-RT-001")
```

</details>

#### does not flag privileged src/lib/ modules

- does not flag privileged src/lib/ modules


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag privileged src/lib/ modules")
val source = "extern fn rt_frobnicate(x: i64) -> i64\n"
val findings = check_raw_rt_access(source, "src/lib/nogc_sync_mut/ffi/example.spl")
assert_equal(findings.len(), 0)
```

</details>

#### does not flag ordinary code with no extern declarations

- does not flag ordinary code with no extern declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag ordinary code with no extern declarations")
val source = "fn add(a: i64, b: i64) -> i64:\n    a + b\n"
val findings = check_raw_rt_access(source, "src/app/cli/example.spl")
assert_equal(findings.len(), 0)
```

</details>

### check_param_tag

#### flags a pub fn with two untagged same-type params

- flags a pub fn with two untagged same-type params
   - Expected: findings.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags a pub fn with two untagged same-type params")
val lines = ["pub fn hash_combine_pair(h1: i64, h2: i64) -> i64:", "    h1 + h2"]
val findings = check_param_tag(lines, "src/lib/nogc_sync_mut/example.spl")
expect(findings.len() > 0).to_equal(true)
assert_equal(findings[0].code, "PTAG001")
```

</details>

#### does not flag a pub fn whose params carry a matching @tag annotation

- does not flag a pub fn whose params carry a matching @tag annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag a pub fn whose params carry a matching @tag annotation")
"""A @tag comment with identical roles for both same-type params
suppresses both PTAG001 (missing tag) and PTAG002 (differing roles)."""
val lines = [
    "# @tag(h1=operand, h2=operand)",
    "pub fn hash_combine_pair(h1: i64, h2: i64) -> i64:",
    "    h1 + h2"
]
val findings = check_param_tag(lines, "src/lib/nogc_sync_mut/example.spl")
assert_equal(findings.len(), 0)
```

</details>

### check_module_init_literal

#### flags a module-level val initialized from a function call

- flags a module-level val initialized from a function call
   - Expected: findings.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags a module-level val initialized from a function call")
val source = "val config = load_config()\n"
val findings = check_module_init_literal(source, "src/app/example.spl")
expect(findings.len() > 0).to_equal(true)
assert_equal(findings[0].code, "MODINIT001")
```

</details>

#### does not flag a module-level val initialized from a literal

- does not flag a module-level val initialized from a literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag a module-level val initialized from a literal")
val source = "val max_retries = 3\n"
val findings = check_module_init_literal(source, "src/app/example.spl")
assert_equal(findings.len(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/tools/lint_checks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering check_raw_rt_access, check_param_tag, check_module_init_literal.
- check_raw_rt_access
- check_param_tag
- check_module_init_literal

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dd1a44a0364191e0ebddc7e1e42d6e9f44e7cd916f2abf7b0ad18b247bded737`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd1a44a0364191e0ebddc7e1e42d6e9f44e7cd916f2abf7b0ad18b247bded737`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd1a44a0364191e0ebddc7e1e42d6e9f44e7cd916f2abf7b0ad18b247bded737`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/tools/lint_checks_spec.spl
mirror: doc/06_spec/01_unit/compiler/tools/lint_checks_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/tools/lint_checks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/tools/lint_checks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/tools/lint_checks_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags an extern rt_* declaration in non-privileged app code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/tools/lint_checks_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag privileged src/lib/ modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/tools/lint_checks_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag ordinary code with no extern declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
