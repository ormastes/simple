# Inventory Classifier Specification

> Validates the five-category module classifier that categorizes every src/lib .spl file as pure-Simple, C-wrapper, SFFI-wrapper, shell-backed, or hw-hook. Uses first-match-wins priority ordering per D-3.

<!-- sdn-diagram:id=inventory_classifier_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=inventory_classifier_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

inventory_classifier_spec -> std
inventory_classifier_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=inventory_classifier_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/app/stats/inventory_classifier_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange — import classifier from module that does not exist yet
val result = classify_module("test/fixtures/pure_simple_example.spl")

# Assert
val is_pure = result == ProviderType.PureSimple
expect(is_pure).to_equal(true)
```

</details>

#### AC-1: classifies a file with extern fn as CWrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_module("test/fixtures/c_wrapper_example.spl")

val is_c = result == ProviderType.CWrapper
expect(is_c).to_equal(true)
```

</details>

#### AC-1: classifies a *_sffi.spl file as SffiWrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_module("test/fixtures/net_sffi.spl")

val is_sffi = result == ProviderType.SffiWrapper
expect(is_sffi).to_equal(true)
```

</details>

#### AC-1: classifies a file with /bin/sh as ShellBacked

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_module("test/fixtures/shell_backed_example.spl")

val is_shell = result == ProviderType.ShellBacked
expect(is_shell).to_equal(true)
```

</details>

#### AC-1: classifies a file with rt_volatile externs as HwHook

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_module("test/fixtures/hw_hook_example.spl")

val is_hw = result == ProviderType.HwHook
expect(is_hw).to_equal(true)
```

</details>

#### AC-1: hw-hook wins over C-wrapper when file has both extern fn and rt_volatile

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First-match-wins: hw-hook has higher priority than C-wrapper
val result = classify_module("src/lib/nogc_sync_mut/io/volatile_ops.spl")

val is_hw = result == ProviderType.HwHook
expect(is_hw).to_equal(true)
```

</details>

### classify_all_modules

#### AC-1: returns a non-empty list for src/lib root

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val results = classify_all_modules("src/lib/")

val count = results.len()
expect(count).to_be_greater_than(0)
```

</details>

### generate_inventory_report

#### AC-1: writes inventory report to specified output path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report_result = generate_inventory_report("src/lib/", "/tmp/test_inventory.md")

val is_ok = report_result.is_ok()
expect(is_ok).to_equal(true)
```

</details>

#### AC-1: report contains all five category headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Plan:** [doc/03_plan/pure_simple_lib_standalone_hw_plan.md](doc/03_plan/pure_simple_lib_standalone_hw_plan.md)


</details>
