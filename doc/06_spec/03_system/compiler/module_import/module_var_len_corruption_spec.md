# Module Var Len Corruption Specification

> Tests covering Module Array .len() Corruption.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Var Len Corruption Specification

## Scenarios

### Module Array .len() Corruption

#### single .len() call (baseline - should work)

#### calls .len() once on [text] array

- calls .len() once on [text] array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls .len() once on [text] array")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_stdout("len_once_text.spl", "0")
```

</details>

#### calls .len() once on [i64] array

- calls .len() once on [i64] array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls .len() once on [i64] array")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_stdout("len_once_i64.spl", "0")
```

</details>

#### double .len() call (KNOWN BUG - corruption)

#### calls .len() twice on [text] array

- calls .len() twice on [text] array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls .len() twice on [text] array")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_known_bug("len_twice_text.spl", ".len() twice on [text] crashes", "0")
```

</details>

#### calls .len() twice on [i64] array

- calls .len() twice on [i64] array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls .len() twice on [i64] array")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_known_bug("len_twice_i64.spl", ".len() twice on [i64] crashes", "0")
```

</details>

#### mixed operations with .len()

#### calls .len() then .push() (KNOWN BUG - single .len() corrupts for all ops)

- calls .len() then .push() (KNOWN BUG - single .len() corrupts for all ops)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls .len() then .push() (KNOWN BUG - single .len() corrupts for all ops)")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_known_bug("len_then_push.spl", ".len() corrupts array for subsequent .push()", "0")
```

</details>

#### calls .push() then .len()

- calls .push() then .len()


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls .push() then .len()")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_known_bug("push_then_len.spl", "push_then_len crashes", "1")
```

</details>

#### cross-function and multi-array

#### calls .len() in two separate function invocations

- calls .len() in two separate function invocations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls .len() in two separate function invocations")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_stdout("len_across_functions.spl", "0")
```

</details>

#### calls .len() on different arrays (one per array)

- calls .len() on different arrays (one per array)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls .len() on different arrays (one per array)")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_stdout("multiple_arrays_len.spl", "0")
```

</details>

#### workaround - cache .len() in local var

#### caches .len() result and reuses cached value

- caches .len() result and reuses cached value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("caches .len() result and reuses cached value")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_stdout("len_cached_workaround.spl", "0")
```

</details>

#### direct run without import (control test)

#### calls .len() twice in directly-run file (KNOWN BUG - also fails without import)

- calls .len() twice in directly-run file (KNOWN BUG - also fails without import)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls .len() twice in directly-run file (KNOWN BUG - also fails without import)")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    # This fixture does NOT import anything - it defines its own array
    # Finding: bug also occurs without import, contradicting initial hypothesis
    _run_and_check_known_bug("direct_run_len_twice.spl", ".len() twice fails even without import", "0")
```

</details>

#### diagnostic - error details on corruption

#### double .len() [text] error mentions type or corruption

- double .len() [text] error mentions type or corruption


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("double .len() [text] error mentions type or corruption")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_diag_type_check("len_twice_text.spl", ".len() twice [text]")
```

</details>

#### double .len() [i64] error mentions type or corruption

- double .len() [i64] error mentions type or corruption


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("double .len() [i64] error mentions type or corruption")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_diag_type_check("len_twice_i64.spl", ".len() twice [i64]")
```

</details>

#### compares single vs double .len() behavior

- compares single vs double .len() behavior


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compares single vs double .len() behavior")
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_diag_compare()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/module_import/module_var_len_corruption_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Module Array .len() Corruption.
- Module Array .len() Corruption

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db785974b70d4a76cbee912f5d1c79da3da85540a9927f76ed49b745463b290a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db785974b70d4a76cbee912f5d1c79da3da85540a9927f76ed49b745463b290a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db785974b70d4a76cbee912f5d1c79da3da85540a9927f76ed49b745463b290a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/module_import/module_var_len_corruption_spec.spl
mirror: doc/06_spec/03_system/compiler/module_import/module_var_len_corruption_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/module_import/module_var_len_corruption_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/module_import/module_var_len_corruption_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/module_import/module_var_len_corruption_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls .len() once on [text] array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/module_import/module_var_len_corruption_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls .len() once on [i64] array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/module_import/module_var_len_corruption_spec.spl:186:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls .len() twice on [text] array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
