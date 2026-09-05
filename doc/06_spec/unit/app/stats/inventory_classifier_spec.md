# Inventory Classifier Specification

> Validates the five-category module classifier that categorizes every src/lib .spl file as pure-Simple, C-wrapper, SFFI-wrapper, shell-backed, or hw-hook. Uses first-match-wins priority ordering per D-3.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inventory Classifier Specification

Validates the five-category module classifier that categorizes every src/lib .spl file as pure-Simple, C-wrapper, SFFI-wrapper, shell-backed, or hw-hook. Uses first-match-wins priority ordering per D-3.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #hw-access-optimization-infra |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Draft |
| Plan | doc/03_plan/pure_simple_lib_standalone_hw_plan.md |
| Source | `test/unit/app/stats/inventory_classifier_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the five-category module classifier that categorizes every src/lib
.spl file as pure-Simple, C-wrapper, SFFI-wrapper, shell-backed, or hw-hook.
Uses first-match-wins priority ordering per D-3.

## Behavior

- hw-hook: file contains @address or @volatile attribute or rt_volatile_*/rt_dma_* externs
- shell-backed: file contains "/bin/sh" or Command::new("sh")
- SFFI-wrapper: filename matches *_sffi.spl or registered in feature_registry
- C-wrapper: file contains any extern fn declaration
- pure-Simple: everything else (default)

## Scenarios

### InventoryClassifier

### classify_module

#### AC-1: classifies a file with no extern fn as PureSimple

- AC-1: classifies a file with no extern fn as PureSimple
   - Expected: is_pure is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: classifies a file with no extern fn as PureSimple")
# Arrange — import classifier from module that does not exist yet
val result = classify_module("test/fixtures/pure_simple_example.spl")

# Assert
val is_pure = result == ProviderType.PureSimple
expect(is_pure).to_equal(true)
```

</details>

#### AC-1: classifies a file with extern fn as CWrapper

- AC-1: classifies a file with extern fn as CWrapper
   - Expected: is_c is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: classifies a file with extern fn as CWrapper")
val result = classify_module("test/fixtures/c_wrapper_example.spl")

val is_c = result == ProviderType.CWrapper
expect(is_c).to_equal(true)
```

</details>

#### AC-1: classifies a *_sffi.spl file as SffiWrapper

- AC-1: classifies a *_sffi.spl file as SffiWrapper
   - Expected: is_sffi is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: classifies a *_sffi.spl file as SffiWrapper")
val result = classify_module("test/fixtures/net_sffi.spl")

val is_sffi = result == ProviderType.SffiWrapper
expect(is_sffi).to_equal(true)
```

</details>

#### AC-1: classifies a file with /bin/sh as ShellBacked

- AC-1: classifies a file with /bin/sh as ShellBacked
   - Expected: is_shell is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: classifies a file with /bin/sh as ShellBacked")
val result = classify_module("test/fixtures/shell_backed_example.spl")

val is_shell = result == ProviderType.ShellBacked
expect(is_shell).to_equal(true)
```

</details>

#### AC-1: classifies a file with rt_volatile externs as HwHook

- AC-1: classifies a file with rt_volatile externs as HwHook
   - Expected: is_hw is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: classifies a file with rt_volatile externs as HwHook")
val result = classify_module("test/fixtures/hw_hook_example.spl")

val is_hw = result == ProviderType.HwHook
expect(is_hw).to_equal(true)
```

</details>

#### AC-1: hw-hook wins over C-wrapper when file has both extern fn and rt_volatile

- AC-1: hw-hook wins over C-wrapper when file has both extern fn and rt_volatile
   - Expected: is_hw is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: hw-hook wins over C-wrapper when file has both extern fn and rt_volatile")
# First-match-wins: hw-hook has higher priority than C-wrapper
val result = classify_module("src/lib/nogc_sync_mut/io/volatile_ops.spl")

val is_hw = result == ProviderType.HwHook
expect(is_hw).to_equal(true)
```

</details>

### classify_all_modules

#### AC-1: returns a non-empty list for src/lib root

- AC-1: returns a non-empty list for src/lib root


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns a non-empty list for src/lib root")
val results = classify_all_modules("src/lib/")

val count = results.len()
expect(count).to_be_greater_than(0)
```

</details>

### generate_inventory_report

#### AC-1: writes inventory report to specified output path

- AC-1: writes inventory report to specified output path
   - Expected: is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: writes inventory report to specified output path")
val report_result = generate_inventory_report("src/lib/", "/tmp/test_inventory.md")

val is_ok = report_result.is_ok()
expect(is_ok).to_equal(true)
```

</details>

#### AC-1: report contains all five category headers

- AC-1: report contains all five category headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: report contains all five category headers")
val report_result = generate_inventory_report("src/lib/", "/tmp/test_inventory_headers.md")
val report_text = report_result.unwrap()

expect(report_text).to_contain("PureSimple")
expect(report_text).to_contain("CWrapper")
expect(report_text).to_contain("SffiWrapper")
expect(report_text).to_contain("ShellBacked")
expect(report_text).to_contain("HwHook")
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


## Related Documentation

- **Plan:** `doc/03_plan/pure_simple_lib_standalone_hw_plan.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eca61b423eafabd4ab1d8ec9bb8d844164fc809d301cd489699108ba77cdc6f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eca61b423eafabd4ab1d8ec9bb8d844164fc809d301cd489699108ba77cdc6f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eca61b423eafabd4ab1d8ec9bb8d844164fc809d301cd489699108ba77cdc6f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/stats/inventory_classifier_spec.spl
mirror: doc/06_spec/unit/app/stats/inventory_classifier_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/stats/inventory_classifier_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/stats/inventory_classifier_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/stats/inventory_classifier_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: classifies a file with no extern fn as PureSimple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/stats/inventory_classifier_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: classifies a file with extern fn as CWrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/stats/inventory_classifier_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: classifies a *_sffi.spl file as SffiWrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
