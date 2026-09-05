# Raw Sffi Call Specification

> Tests covering SFFI009: raw calls require minimal ffi-unsafe scope.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Raw Sffi Call Specification

## Scenarios

### SFFI009: raw calls require minimal ffi-unsafe scope

#### reports a raw extern call in an ordinary function

- reports a raw extern call in an ordinary function
   - Expected: findings.len() equals `1`
   - Expected: findings[0].code equals `SFFI009`
   - Expected: findings[0].line_num equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports a raw extern call in an ordinary function")
"""An unannotated caller must be rejected at the source boundary."""
val source = "extern fn rt_widget_open() -> i64\n\nfn open_widget() -> i64:\n    rt_widget_open()\n"
val findings = check_raw_sffi_calls(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].code).to_equal("SFFI009")
expect(findings[0].line_num).to_equal(4)
```

</details>

#### accepts a minimal explicitly ffi-unsafe helper

- accepts a minimal explicitly ffi-unsafe helper
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts a minimal explicitly ffi-unsafe helper")
"""The canonical ffi capability discharges the raw-call lint locally."""
val source = "extern fn rt_widget_open() -> i64\n\n@unsafe(reason: \"raw widget ABI\", capabilities: [ffi])\nfn _open_raw() -> i64:\n    rt_widget_open()\n"
val findings = check_raw_sffi_calls(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### accepts only calls nested in a lexical ffi-unsafe block

- accepts only calls nested in a lexical ffi-unsafe block
   - Expected: check_raw_sffi_calls(source, "src/app/demo.spl").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts only calls nested in a lexical ffi-unsafe block")
"""An inline block avoids an extra hot-path helper call while keeping
the validation and lift code outside foreign authority."""
val source = "extern fn rt_widget_open() -> i64\n\nfn open_widget() -> i64:\n    val raw = unsafe(capabilities: [ffi]):\n        rt_widget_open()\n    if raw <= 0:\n        return -1\n    raw\n"
expect(check_raw_sffi_calls(source, "src/app/demo.spl").len()).to_equal(0)
```

</details>

#### does not let lexical ffi authority escape its indentation scope

- does not let lexical ffi authority escape its indentation scope
   - Expected: findings.len() equals `1`
   - Expected: findings[0].line_num equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not let lexical ffi authority escape its indentation scope")
"""A sibling raw call after the block remains a violation."""
val source = "extern fn rt_widget_open() -> i64\n\nfn open_widget() -> i64:\n    unsafe(capabilities: [ffi]):\n        rt_widget_open()\n    rt_widget_open()\n"
val findings = check_raw_sffi_calls(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].line_num).to_equal(6)
```

</details>

#### does not accept an unrelated unsafe capability

- does not accept an unrelated unsafe capability
   - Expected: findings.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not accept an unrelated unsafe capability")
"""Raw-pointer authority does not imply permission to invoke foreign code."""
val source = "extern fn rt_widget_open() -> i64\n\n@unsafe(reason: \"memory only\", capabilities: [raw_ptr])\nfn _open_raw() -> i64:\n    rt_widget_open()\n"
val findings = check_raw_sffi_calls(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
```

</details>

#### does not confuse a longer identifier with the extern name

- does not confuse a longer identifier with the extern name
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not confuse a longer identifier with the extern name")
"""Identifier matching must avoid false positives on ordinary functions."""
val source = "extern fn rt_open() -> i64\n\nfn safe() -> i64:\n    my_rt_open()\n"
val findings = check_raw_sffi_calls(source, "src/app/demo.spl")
expect(findings.len()).to_equal(0)
```

</details>

#### reports an imported raw SFFI call outside authority

- reports an imported raw SFFI call outside authority
   - Expected: findings.len() equals `1`
   - Expected: findings[0].line_num equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports an imported raw SFFI call outside authority")
"""Imported raw symbols must not bypass the declaration-local census."""
val source = "use std.thread_sffi.{{spl_thread_sleep}}\n\nfn pause():\n    spl_thread_sleep(1)\n"
val findings = check_raw_sffi_calls(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].line_num).to_equal(4)
```

</details>

#### accepts an imported raw SFFI call in a lexical block

- accepts an imported raw SFFI call in a lexical block
   - Expected: check_raw_sffi_calls(source, "src/app/demo.spl").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts an imported raw SFFI call in a lexical block")
"""The imported raw symbol retains its FFI effect at the call site."""
val source = "use std.thread_sffi.{{\n    spl_thread_sleep, spl_thread_join\n}}\n\nfn pause():\n    unsafe(capabilities: [ffi]):\n        spl_thread_sleep(1)\n"
expect(check_raw_sffi_calls(source, "src/app/demo.spl").len()).to_equal(0)
```

</details>

#### maps to deny in robust and critical profiles

- maps to deny in robust and critical profiles
   - Expected: map_lint_code_to_config_name("SFFI009") equals `raw_sffi_call`
   - Expected: robust["raw_sffi_call"] equals `deny`
   - Expected: critical["raw_sffi_call"] equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps to deny in robust and critical profiles")
"""Assurance profiles make missing ffi scope a release-blocking error."""
expect(map_lint_code_to_config_name("SFFI009")).to_equal("raw_sffi_call")
val robust = profile_default_levels(LintProfile.Robust)
val critical = profile_default_levels(LintProfile.Critical)
expect(robust["raw_sffi_call"]).to_equal("deny")
expect(critical["raw_sffi_call"]).to_equal("deny")
```

</details>

#### reports an extern declaration that lacks ffi authority

- reports an extern declaration that lacks ffi authority
   - Expected: findings.len() equals `1`
   - Expected: findings[0].code equals `SFFI010`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports an extern declaration that lacks ffi authority")
"""Declarations are ABI assertions even when the function is never called."""
val findings = check_raw_sffi_declarations(
    "extern fn rt_widget_open() -> i64\n", "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].code).to_equal("SFFI010")
```

</details>

#### accepts an explicitly ffi-unsafe extern declaration

- accepts an explicitly ffi-unsafe extern declaration
   - Expected: check_raw_sffi_declarations(source, "src/app/demo.spl").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("accepts an explicitly ffi-unsafe extern declaration")
"""The declaration carries authority independently of its safe wrapper."""
val source = "@unsafe(reason: \"foreign ABI\", capabilities: [ffi])\nextern fn rt_widget_open() -> i64\n"
expect(check_raw_sffi_declarations(source, "src/app/demo.spl").len()).to_equal(0)
```

</details>

#### checks attribute-style foreign declarations

- checks attribute-style foreign declarations
   - Expected: findings.len() equals `1`
   - Expected: findings[0].code equals `SFFI010`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("checks attribute-style foreign declarations")
"""Legacy @extern syntax cannot bypass the same declaration policy."""
val source = "@extern(\"runtime\", \"rt_widget_open\")\nfn rt_widget_open() -> i64:\n    0\n"
val findings = check_raw_sffi_declarations(source, "src/app/demo.spl")
expect(findings.len()).to_equal(1)
expect(findings[0].code).to_equal("SFFI010")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/raw_sffi_call_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SFFI009: raw calls require minimal ffi-unsafe scope.
- SFFI009: raw calls require minimal ffi-unsafe scope

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `76b720857313a38dc1e5998270a75e4eb1f2fee05c664f7fe621ae77b8f5dab2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `76b720857313a38dc1e5998270a75e4eb1f2fee05c664f7fe621ae77b8f5dab2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `76b720857313a38dc1e5998270a75e4eb1f2fee05c664f7fe621ae77b8f5dab2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/lint/raw_sffi_call_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/raw_sffi_call_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/lint/raw_sffi_call_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/raw_sffi_call_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/raw_sffi_call_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/raw_sffi_call_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a raw extern call in an ordinary function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/raw_sffi_call_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a minimal explicitly ffi-unsafe helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/raw_sffi_call_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only calls nested in a lexical ffi-unsafe block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
