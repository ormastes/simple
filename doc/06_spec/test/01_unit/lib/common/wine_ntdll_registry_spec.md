# Wine Ntdll Registry Specification

> 1. wine ntdll registry hive default

<!-- sdn-diagram:id=wine_ntdll_registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_ntdll_registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_ntdll_registry_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_ntdll_registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Ntdll Registry Specification

## Scenarios

### Wine NTDLL registry bridge

#### executes bounded key open, value query, and close

1. wine ntdll registry hive default
   - Expected: result.ok is true
   - Expected: result.handle equals `0x600`
   - Expected: result.value equals `C:\\windows`
   - Expected: result.operations equals `NtOpenKey NtQueryValueKey NtClose`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_ntdll_execute_registry_query(
    ["NtOpenKey", "NtQueryValueKey", "NtClose"],
    wine_ntdll_registry_hive_default(),
    "\\Registry\\Machine\\Software\\Wine",
    "InstallRoot"
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x600)
expect(result.value).to_equal("C:\\windows")
expect(result.operations).to_equal("NtOpenKey NtQueryValueKey NtClose")
```

</details>

#### keeps NTDLL registry dispatch ordered and bounded

1. wine ntdll registry hive default
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `ntdll-registry-sequence-expected:NtOpenKey`
2. wine ntdll registry hive default
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:NtCreateFile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_ntdll_execute_registry_query(
    ["NtQueryValueKey", "NtOpenKey", "NtClose"],
    wine_ntdll_registry_hive_default(),
    "\\Registry\\Machine\\Software\\Wine",
    "InstallRoot"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("ntdll-registry-sequence-expected:NtOpenKey")

val wrong_family = wine_ntdll_execute_registry_query(
    ["NtOpenKey", "NtQueryValueKey", "NtCreateFile"],
    wine_ntdll_registry_hive_default(),
    "\\Registry\\Machine\\Software\\Wine",
    "InstallRoot"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### rejects missing registry values

1. wine ntdll registry hive default
   - Expected: result.ok is false
   - Expected: result.error equals `NtQueryValueKey:value-not-found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_ntdll_execute_registry_query(
    ["NtOpenKey", "NtQueryValueKey", "NtClose"],
    wine_ntdll_registry_hive_default(),
    "\\Registry\\Machine\\Software\\Wine",
    "Missing"
)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("NtQueryValueKey:value-not-found")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_ntdll_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NTDLL registry bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
