# Wine Ntdll Loader Specification

> 1.  table

<!-- sdn-diagram:id=wine_ntdll_loader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_ntdll_loader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_ntdll_loader_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_ntdll_loader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Ntdll Loader Specification

## Scenarios

### Wine NTDLL loader bridge

#### executes a bounded Ldr module and procedure resolution sequence

1.  table
   - Expected: result.ok is true
   - Expected: result.handle equals `0x701`
   - Expected: result.proc equals `kernel32.dll!GetProcAddress`
   - Expected: result.operations equals `LdrLoadDll LdrGetProcedureAddress LdrUnloadDll`
   - Expected: result.table.next_handle equals `0x703`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_ntdll_execute_loader_resolution(
    ["LdrLoadDll", "LdrGetProcedureAddress", "LdrUnloadDll"],
    _table(),
    "KERNEL32.dll",
    "GetProcAddress"
)

expect(result.ok).to_equal(true)
expect(result.handle).to_equal(0x701)
expect(result.proc).to_equal("kernel32.dll!GetProcAddress")
expect(result.operations).to_equal("LdrLoadDll LdrGetProcedureAddress LdrUnloadDll")
expect(result.table.next_handle).to_equal(0x703)
```

</details>

#### keeps NTDLL loader dispatch ordered and bounded

1.  table
   - Expected: out_of_order.ok is false
   - Expected: out_of_order.error equals `ntdll-loader-sequence-expected:LdrLoadDll`
2.  table
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:NtCreateFile`
3.  table
   - Expected: wrong_count.ok is false
   - Expected: wrong_count.error equals `ntdll-loader-sequence-count-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out_of_order = wine_ntdll_execute_loader_resolution(
    ["LdrGetProcedureAddress", "LdrLoadDll", "LdrUnloadDll"],
    _table(),
    "kernel32.dll",
    "GetProcAddress"
)
expect(out_of_order.ok).to_equal(false)
expect(out_of_order.error).to_equal("ntdll-loader-sequence-expected:LdrLoadDll")

val wrong_family = wine_ntdll_execute_loader_resolution(
    ["LdrLoadDll", "NtCreateFile", "LdrUnloadDll"],
    _table(),
    "kernel32.dll",
    "GetProcAddress"
)
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:NtCreateFile")

val wrong_count = wine_ntdll_execute_loader_resolution(
    ["LdrLoadDll", "LdrGetProcedureAddress"],
    _table(),
    "kernel32.dll",
    "GetProcAddress"
)
expect(wrong_count.ok).to_equal(false)
expect(wrong_count.error).to_equal("ntdll-loader-sequence-count-mismatch")
```

</details>

#### reports missing modules, missing procedures, and invalid handles

1.  table
   - Expected: missing_module.ok is false
   - Expected: missing_module.error equals `LdrLoadDll:module-not-found`
2.  table
   - Expected: missing_proc.ok is false
   - Expected: missing_proc.error equals `LdrGetProcedureAddress:proc-not-found`
   - Expected: invalid_handle.ok is false
   - Expected: invalid_handle.error equals `invalid-module-handle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_module = wine_ntdll_execute_loader_resolution(
    ["LdrLoadDll", "LdrGetProcedureAddress", "LdrUnloadDll"],
    _table(),
    "advapi32.dll",
    "RegOpenKeyExW"
)
expect(missing_module.ok).to_equal(false)
expect(missing_module.error).to_equal("LdrLoadDll:module-not-found")

val missing_proc = wine_ntdll_execute_loader_resolution(
    ["LdrLoadDll", "LdrGetProcedureAddress", "LdrUnloadDll"],
    _table(),
    "kernel32.dll",
    "UnknownProc"
)
expect(missing_proc.ok).to_equal(false)
expect(missing_proc.error).to_equal("LdrGetProcedureAddress:proc-not-found")

val invalid_handle = wine_ntdll_ldr_get_procedure_address(_table(), 0x999, "kernel32.dll", "GetProcAddress")
expect(invalid_handle.ok).to_equal(false)
expect(invalid_handle.error).to_equal("invalid-module-handle")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_ntdll_loader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NTDLL loader bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
