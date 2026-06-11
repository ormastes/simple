# Wine Advapi32 Registry Specification

> <details>

<!-- sdn-diagram:id=wine_advapi32_registry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_advapi32_registry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_advapi32_registry_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_advapi32_registry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Advapi32 Registry Specification

## Scenarios

### Wine ADVAPI32 registry bridge

#### executes a bounded registry create-open-set-query-close roundtrip

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_advapi32_execute_registry_roundtrip(["RegCreateKeyExW", "RegOpenKeyExW", "RegSetValueExW", "RegQueryValueExW", "RegCloseKey"], "HKEY_CURRENT_USER", "Software\\SimpleOS\\Wine", "InstallRoot", "C:\\simple")
expect(result.ok).to_equal(true)
expect(result.root).to_equal("HKEY_CURRENT_USER")
expect(result.key).to_equal("Software\\SimpleOS\\Wine")
expect(result.name).to_equal("InstallRoot")
expect(result.value).to_equal("C:\\simple")
expect(result.handle).to_be_greater_than(0)
expect(result.operations).to_contain("RegCreateKeyExW")
expect(result.operations).to_contain("RegQueryValueExW")
expect(result.operations).to_contain("RegCloseKey")
```

</details>

#### keeps registry dispatch ordered and bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_advapi32_execute_registry_roundtrip(["RegOpenKeyExW", "RegCreateKeyExW", "RegSetValueExW", "RegQueryValueExW", "RegCloseKey"], "HKEY_CURRENT_USER", "Software", "Name", "Value")
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("advapi32-registry-sequence-expected:RegCreateKeyExW")

val unsupported = wine_advapi32_execute_registry_roundtrip(["RegCreateKeyExW", "RegOpenKeyExW", "RegSetValueExW", "GetMessageW", "RegCloseKey"], "HKEY_CURRENT_USER", "Software", "Name", "Value")
expect(unsupported.ok).to_equal(false)
expect(unsupported.error).to_equal("bridge-unsupported:GetMessageW")

val invalid = wine_advapi32_execute_registry_roundtrip(["RegCreateKeyExW", "RegOpenKeyExW", "RegSetValueExW", "RegQueryValueExW", "RegCloseKey"], "HKEY_CLASSES_ROOT", "Software", "Name", "Value")
expect(invalid.ok).to_equal(false)
expect(invalid.error).to_equal("unsupported-root:HKEY_CLASSES_ROOT")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_advapi32_registry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine ADVAPI32 registry bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
