# Wine Nt Import Specification

> <details>

<!-- sdn-diagram:id=wine_nt_import_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_nt_import_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_nt_import_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_nt_import_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Nt Import Specification

## Scenarios

### Wine NT import resolver gate

#### recognizes the minimal hello.exe KERNEL32 import set

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_nt_import_required_symbols_for_hello().len()).to_equal(3)
expect(wine_nt_import_dll_gate("KERNEL32.dll")).to_equal("ready")
```

</details>

#### rejects unsupported DLLs before symbol checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_nt_import_hello_gate("USER32.dll", ["GetStdHandle", "WriteFile", "ExitProcess"])).to_equal("unsupported-dll:USER32.dll")
```

</details>

#### reports the first missing minimal console symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_nt_import_hello_gate("KERNEL32.dll", ["GetStdHandle"])).to_equal("missing-symbol:WriteFile")
```

</details>

#### accepts the minimal console symbol set

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_nt_import_hello_gate("kernel32.dll", ["GetStdHandle", "WriteFile", "ExitProcess"])).to_equal("ready")
```

</details>

#### requires the known hello import bindings to target expected name RVAs

1. PeImportSymbolBinding
2. PeImportSymbolBinding
3. PeImportSymbolBinding
   - Expected: wine_nt_import_hello_binding_gate("KERNEL32.dll", bindings) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bindings = [
    PeImportSymbolBinding(symbol: "GetStdHandle", name_rva: 0x2080),
    PeImportSymbolBinding(symbol: "WriteFile", name_rva: 0x20a0),
    PeImportSymbolBinding(symbol: "ExitProcess", name_rva: 0x20c0)
]
expect(wine_nt_import_hello_binding_gate("KERNEL32.dll", bindings)).to_equal("ready")
```

</details>

#### returns a structured hello binding plan

1. PeImportSymbolBinding
2. PeImportSymbolBinding
3. PeImportSymbolBinding
   - Expected: plan.ok is true
   - Expected: plan.dll equals `kernel32.dll`
   - Expected: plan.call_sequence equals `GetStdHandle WriteFile ExitProcess`
   - Expected: plan.binding_count equals `3`
   - Expected: plan.get_std_handle_rva equals `0x2080`
   - Expected: plan.write_file_rva equals `0x20a0`
   - Expected: plan.exit_process_rva equals `0x20c0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bindings = [
    PeImportSymbolBinding(symbol: "GetStdHandle", name_rva: 0x2080),
    PeImportSymbolBinding(symbol: "WriteFile", name_rva: 0x20a0),
    PeImportSymbolBinding(symbol: "ExitProcess", name_rva: 0x20c0)
]
val plan = wine_nt_import_hello_binding_plan("KERNEL32.dll", bindings)
expect(plan.ok).to_equal(true)
expect(plan.dll).to_equal("kernel32.dll")
expect(plan.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(plan.binding_count).to_equal(3)
expect(plan.get_std_handle_rva).to_equal(0x2080)
expect(plan.write_file_rva).to_equal(0x20a0)
expect(plan.exit_process_rva).to_equal(0x20c0)
```

</details>

#### rejects mismatched hello import binding targets

1. PeImportSymbolBinding
2. PeImportSymbolBinding
3. PeImportSymbolBinding
   - Expected: wine_nt_import_hello_binding_gate("KERNEL32.dll", bindings) equals `binding-target-mismatch:WriteFile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bindings = [
    PeImportSymbolBinding(symbol: "GetStdHandle", name_rva: 0x2080),
    PeImportSymbolBinding(symbol: "WriteFile", name_rva: 0x2080),
    PeImportSymbolBinding(symbol: "ExitProcess", name_rva: 0x20c0)
]
expect(wine_nt_import_hello_binding_gate("KERNEL32.dll", bindings)).to_equal("binding-target-mismatch:WriteFile")
```

</details>

#### binds KERNEL32 module-loader imports to module exports

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_nt_import_kernel32_module_loader_binding_gate("KERNEL32.dll", _module_loader_bindings(), _module_table())).to_equal("ready")

val plan = wine_nt_import_kernel32_module_loader_binding_plan("KERNEL32.dll", _module_loader_bindings(), _module_table())
expect(plan.ok).to_equal(true)
expect(plan.dll).to_equal("kernel32.dll")
expect(plan.binding_count).to_equal(4)
expect(plan.call_sequence).to_equal("GetModuleHandleW LoadLibraryW GetProcAddress FreeLibrary")
expect(plan.module_handle).to_equal(0x120)
expect(plan.get_module_handle_name_rva).to_equal(0x2140)
expect(plan.get_module_handle_proc_address).to_equal(0x120000 + 1)
expect(plan.get_proc_address_proc_address).to_equal(0x120000 + 3)
```

</details>

#### rejects incomplete or unexported module-loader import bindings

1. PeImportSymbolBinding
2. PeImportSymbolBinding
3. PeImportSymbolBinding
   - Expected: wine_nt_import_kernel32_module_loader_binding_gate("KERNEL32.dll", missing, _module_table()) equals `missing-binding:FreeLibrary`
   - Expected: missing_module equals `unsupported-dll:USER32.dll`
   - Expected: wine_nt_import_kernel32_module_loader_binding_gate("KERNEL32.dll", _module_loader_bindings(), incomplete_exports) equals `module-loader-export:FreeLibrary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = [
    PeImportSymbolBinding(symbol: "GetModuleHandleW", name_rva: 0x2140),
    PeImportSymbolBinding(symbol: "LoadLibraryW", name_rva: 0x2160),
    PeImportSymbolBinding(symbol: "GetProcAddress", name_rva: 0x2180)
]
expect(wine_nt_import_kernel32_module_loader_binding_gate("KERNEL32.dll", missing, _module_table())).to_equal("missing-binding:FreeLibrary")

val missing_module = wine_nt_import_kernel32_module_loader_binding_gate("USER32.dll", _module_loader_bindings(), _module_table())
expect(missing_module).to_equal("unsupported-dll:USER32.dll")

val incomplete_exports = wine_kernel32_module_table_add_module(wine_kernel32_module_table_new(), "kernel32.dll", ["GetModuleHandleW", "LoadLibraryW", "GetProcAddress"])
expect(wine_nt_import_kernel32_module_loader_binding_gate("KERNEL32.dll", _module_loader_bindings(), incomplete_exports)).to_equal("module-loader-export:FreeLibrary")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_nt_import_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NT import resolver gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
