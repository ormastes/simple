# Wine Ntdll Object Namespace Specification

> 1. wine ntdll object namespace default

<!-- sdn-diagram:id=wine_ntdll_object_namespace_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_ntdll_object_namespace_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_ntdll_object_namespace_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_ntdll_object_namespace_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Ntdll Object Namespace Specification

## Scenarios

### Wine NTDLL object namespace bridge

#### executes bounded directory object open, query, and close

1. wine ntdll object namespace default
   - Expected: result.ok is true
   - Expected: result.handle equals `0x500`
   - Expected: result.entries equals `kernel32.dll ntdll.dll user32.dll`
   - Expected: result.operations equals `NtOpenDirectoryObject NtQueryDirectoryObject NtClose`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_ntdll_execute_object_namespace(
    ["NtOpenDirectoryObject", "NtQueryDirectoryObject", "NtClose"],
    wine_ntdll_object_namespace_default(),
    "\\KnownDlls"
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x500)
expect(result.entries).to_equal("kernel32.dll ntdll.dll user32.dll")
expect(result.operations).to_equal("NtOpenDirectoryObject NtQueryDirectoryObject NtClose")
```

</details>

#### keeps object namespace dispatch ordered and bounded

1. wine ntdll object namespace default
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `ntdll-object-namespace-sequence-expected:NtOpenDirectoryObject`
2. wine ntdll object namespace default
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:NtCreateFile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_ntdll_execute_object_namespace(
    ["NtQueryDirectoryObject", "NtOpenDirectoryObject", "NtClose"],
    wine_ntdll_object_namespace_default(),
    "\\KnownDlls"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("ntdll-object-namespace-sequence-expected:NtOpenDirectoryObject")

val wrong_family = wine_ntdll_execute_object_namespace(
    ["NtOpenDirectoryObject", "NtQueryDirectoryObject", "NtCreateFile"],
    wine_ntdll_object_namespace_default(),
    "\\KnownDlls"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:NtCreateFile")
```

</details>

#### rejects unknown object directories

1. wine ntdll object namespace default
   - Expected: result.ok is false
   - Expected: result.error equals `NtOpenDirectoryObject:directory-not-found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_ntdll_execute_object_namespace(
    ["NtOpenDirectoryObject", "NtQueryDirectoryObject", "NtClose"],
    wine_ntdll_object_namespace_default(),
    "\\Missing"
)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("NtOpenDirectoryObject:directory-not-found")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_ntdll_object_namespace_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NTDLL object namespace bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
