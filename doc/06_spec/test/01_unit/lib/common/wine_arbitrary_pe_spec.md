# Wine Arbitrary Pe Specification

> <details>

<!-- sdn-diagram:id=wine_arbitrary_pe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_arbitrary_pe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_arbitrary_pe_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_arbitrary_pe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Arbitrary Pe Specification

## Scenarios

### Wine arbitrary PE probe and hello.exe regression

#### wine_hello_exe_probe still works for hello.exe data (regression AC-10)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _known_hello_exe_fixture()
val result = wine_hello_exe_probe(data, _verified_dispatch_gates())
expect(result.status).to_equal("executed")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(result.exit_code).to_equal(0)
```

</details>

#### wine_arbitrary_pe_probe rejects empty data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_arbitrary_pe_probe([], _verified_gates())
expect(result.status).to_equal("rejected")
```

</details>

#### wine_arbitrary_pe_probe rejects non-PE data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bad: [u8] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]
val result = wine_arbitrary_pe_probe(bad, _verified_gates())
expect(result.status).to_equal("rejected")
```

</details>

#### wine_arbitrary_pe_probe accepts valid PE with implemented imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _minimal_pe64_console_with_resolved_imports()
val result = wine_arbitrary_pe_probe(data, _verified_gates())
expect(result.status).to_equal("accepted")
```

</details>

#### wine_arbitrary_pe_probe returns partial for unimplemented imports

1. var data =  minimal pe64 console with resolved imports
2. data =  put import name
3. data =  put import name
4. data =  put import name
   - Expected: result.status equals `partial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Start from the resolved-imports fixture (passes section/directory/import gates)
# but replace the import symbol names with unimplemented NT functions
var data = _minimal_pe64_console_with_resolved_imports()
data = _put_import_name(data, 0x280, "NtQueryVirtualMemory")
data = _put_import_name(data, 0x2a0, "NtMapViewOfSection")
data = _put_import_name(data, 0x2c0, "NtAllocateVirtualMemory")
val result = wine_arbitrary_pe_probe(data, _verified_gates())
expect(result.status).to_equal("partial")
expect(result.error).to_contain("unimplemented-imports")
```

</details>

#### wine_arbitrary_pe_can_probe returns true for accepted PE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _minimal_pe64_console_with_resolved_imports()
val can = wine_arbitrary_pe_can_probe(data, _verified_gates())
expect(can).to_equal(true)
```

</details>

#### wine_hello_exe_can_execute still works (regression)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _known_hello_exe_fixture()
val can = wine_hello_exe_can_execute(data, _verified_dispatch_gates())
expect(can).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_arbitrary_pe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine arbitrary PE probe and hello.exe regression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
