# Wine Nt Dispatch Table Specification

> <details>

<!-- sdn-diagram:id=wine_nt_dispatch_table_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_nt_dispatch_table_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_nt_dispatch_table_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_nt_dispatch_table_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Nt Dispatch Table Specification

## Scenarios

### wine_nt_dispatch_table

#### has 22+ entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = nt_dispatch_table_count()
expect(count >= 22).to_equal(true)
```

</details>

#### has 16+ implemented entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = nt_dispatch_table_implemented_count()
expect(count >= 16).to_equal(true)
```

</details>

#### lists all entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all = nt_dispatch_table_list_all()
expect(all.len() >= 22).to_equal(true)
```

</details>

#### lists implemented entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val impl_list = nt_dispatch_table_list_implemented()
expect(impl_list.len() >= 16).to_equal(true)
```

</details>

#### looks up CreateFileW entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = nt_dispatch_table_lookup("CreateFileW")
expect(entry.symbol).to_equal("CreateFileW")
expect(entry.dll).to_equal("kernel32.dll")
expect(entry.category).to_equal("file")
expect(entry.implemented).to_equal(true)
```

</details>

#### looks up unimplemented MessageBoxW entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = nt_dispatch_table_lookup("MessageBoxW")
expect(entry.symbol).to_equal("MessageBoxW")
expect(entry.dll).to_equal("user32.dll")
expect(entry.implemented).to_equal(false)
```

</details>

#### returns empty entry for unknown symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = nt_dispatch_table_lookup("FakeFunction")
expect(entry.dll).to_equal("")
expect(entry.implemented).to_equal(false)
```

</details>

#### CreateFileW returns valid handle

1. nt dispatch table reset
   - Expected: result.is_ok is true
   - Expected: result.symbol equals `CreateFileW`
   - Expected: result.i64_value >= 100 is true
   - Expected: result.text_value equals `C:\\test.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val result = nt_dispatch_table_call("CreateFileW", 0, 0, "C:\\test.txt")
expect(result.is_ok).to_equal(true)
expect(result.symbol).to_equal("CreateFileW")
expect(result.i64_value >= 100).to_equal(true)
expect(result.text_value).to_equal("C:\\test.txt")
```

</details>

#### ReadFile and WriteFile round-trip

1. nt dispatch table reset
   - Expected: opened.is_ok is true
   - Expected: written.is_ok is true
   - Expected: written.i64_value equals `5`
   - Expected: read.is_ok is true
   - Expected: read.i64_value equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val opened = nt_dispatch_table_call("CreateFileW", 0, 0, "C:\\data.bin")
expect(opened.is_ok).to_equal(true)
val handle = opened.i64_value

val written = nt_dispatch_table_call("WriteFile", handle, 5, "hello")
expect(written.is_ok).to_equal(true)
expect(written.i64_value).to_equal(5)

val read = nt_dispatch_table_call("ReadFile", handle, 5, "")
expect(read.is_ok).to_equal(true)
expect(read.i64_value).to_equal(5)
```

</details>

#### CloseHandle marks handle closed

1. nt dispatch table reset
   - Expected: opened.is_ok is true
   - Expected: closed.is_ok is true
   - Expected: double_close.is_ok is false
   - Expected: double_close.error equals `already-closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val opened = nt_dispatch_table_call("CreateFileW", 0, 0, "C:\\close_test.txt")
expect(opened.is_ok).to_equal(true)
val handle = opened.i64_value

val closed = nt_dispatch_table_call("CloseHandle", handle, 0, "")
expect(closed.is_ok).to_equal(true)

val double_close = nt_dispatch_table_call("CloseHandle", handle, 0, "")
expect(double_close.is_ok).to_equal(false)
expect(double_close.error).to_equal("already-closed")
```

</details>

#### VirtualAlloc returns positive address and VirtualFree succeeds

1. nt dispatch table reset
   - Expected: alloc.is_ok is true
   - Expected: alloc.i64_value > 0 is true
   - Expected: freed.is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val alloc = nt_dispatch_table_call("VirtualAlloc", 0, 4096, "")
expect(alloc.is_ok).to_equal(true)
expect(alloc.i64_value > 0).to_equal(true)

val freed = nt_dispatch_table_call("VirtualFree", alloc.i64_value, 0, "")
expect(freed.is_ok).to_equal(true)
```

</details>

#### HeapCreate HeapAlloc HeapFree lifecycle

1. nt dispatch table reset
   - Expected: heap.is_ok is true
   - Expected: block.is_ok is true
   - Expected: block.i64_value > 0 is true
   - Expected: freed.is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val heap = nt_dispatch_table_call("HeapCreate", 0, 0, "")
expect(heap.is_ok).to_equal(true)
val heap_handle = heap.i64_value

val block = nt_dispatch_table_call("HeapAlloc", heap_handle, 64, "")
expect(block.is_ok).to_equal(true)
expect(block.i64_value > 0).to_equal(true)

val freed = nt_dispatch_table_call("HeapFree", heap_handle, block.i64_value, "")
expect(freed.is_ok).to_equal(true)
```

</details>

#### GetProcessHeap returns valid handle

1. nt dispatch table reset
   - Expected: result.is_ok is true
   - Expected: result.i64_value equals `0x70000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val result = nt_dispatch_table_call("GetProcessHeap", 0, 0, "")
expect(result.is_ok).to_equal(true)
expect(result.i64_value).to_equal(0x70000000)
```

</details>

#### GetProcessHeap HeapAlloc HeapFree on process heap

1. nt dispatch table reset
   - Expected: heap.is_ok is true
   - Expected: block.is_ok is true
   - Expected: block.i64_value equals `0x71000000`
   - Expected: freed.is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val heap = nt_dispatch_table_call("GetProcessHeap", 0, 0, "")
expect(heap.is_ok).to_equal(true)

val block = nt_dispatch_table_call("HeapAlloc", heap.i64_value, 32, "")
expect(block.is_ok).to_equal(true)
expect(block.i64_value).to_equal(0x71000000)

val freed = nt_dispatch_table_call("HeapFree", heap.i64_value, block.i64_value, "")
expect(freed.is_ok).to_equal(true)
```

</details>

#### GetCommandLineW returns text

1. nt dispatch table reset
   - Expected: result.is_ok is true
   - Expected: result.text_value equals `simple.exe`
   - Expected: result.i64_value > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val result = nt_dispatch_table_call("GetCommandLineW", 0, 0, "")
expect(result.is_ok).to_equal(true)
expect(result.text_value).to_equal("simple.exe")
expect(result.i64_value > 0).to_equal(true)
```

</details>

#### GetModuleHandleW returns handle for kernel32

1. nt dispatch table reset
   - Expected: result.is_ok is true
   - Expected: result.i64_value equals `0x10000`
   - Expected: result.text_value equals `kernel32.dll`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val result = nt_dispatch_table_call("GetModuleHandleW", 0, 0, "kernel32.dll")
expect(result.is_ok).to_equal(true)
expect(result.i64_value).to_equal(0x10000)
expect(result.text_value).to_equal("kernel32.dll")
```

</details>

#### LoadLibraryExW and GetProcAddress round-trip

1. nt dispatch table reset
   - Expected: loaded.is_ok is true
   - Expected: proc.is_ok is true
   - Expected: proc.text_value equals `GetProcAddress`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val loaded = nt_dispatch_table_call("LoadLibraryExW", 0, 0, "kernel32.dll")
expect(loaded.is_ok).to_equal(true)
val mod_handle = loaded.i64_value

val proc = nt_dispatch_table_call("GetProcAddress", mod_handle, 0, "GetProcAddress")
expect(proc.is_ok).to_equal(true)
expect(proc.text_value).to_equal("GetProcAddress")
```

</details>

#### unimplemented calls return structured error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = nt_dispatch_table_call("MessageBoxW", 0, 0, "")
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("not-implemented:MessageBoxW")
expect(result.symbol).to_equal("MessageBoxW")
expect(result.category).to_equal("user32")
```

</details>

#### unknown symbol returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = nt_dispatch_table_call("FakeAPI", 0, 0, "")
expect(result.is_ok).to_equal(false)
expect(result.error).to_equal("unknown-symbol:FakeAPI")
```

</details>

#### wine_nt_bridge_dispatch_call routes new symbols correctly

1. nt dispatch table reset
   - Expected: result.ok is true
   - Expected: result.symbol equals `CreateFileW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val result = wine_nt_bridge_dispatch_call("CreateFileW", 0, "C:\\bridge_test.txt", 0)
expect(result.ok).to_equal(true)
expect(result.symbol).to_equal("CreateFileW")
```

</details>

#### wine_nt_bridge_dispatch_call routes VirtualAlloc

1. nt dispatch table reset
   - Expected: result.ok is true
   - Expected: result.symbol equals `VirtualAlloc`
   - Expected: result.i64_value > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val result = wine_nt_bridge_dispatch_call("VirtualAlloc", 0, "", 4096)
expect(result.ok).to_equal(true)
expect(result.symbol).to_equal("VirtualAlloc")
expect(result.i64_value > 0).to_equal(true)
```

</details>

#### wine_nt_bridge_dispatch_call routes HeapCreate

1. nt dispatch table reset
   - Expected: result.ok is true
   - Expected: result.symbol equals `HeapCreate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nt_dispatch_table_reset()
val result = wine_nt_bridge_dispatch_call("HeapCreate", 0, "", 0)
expect(result.ok).to_equal(true)
expect(result.symbol).to_equal("HeapCreate")
```

</details>

#### existing bridge GetStdHandle still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_nt_bridge_dispatch_call("GetStdHandle", 0, "", wine_nt_bridge_stdout_handle())
expect(result.ok).to_equal(true)
expect(result.symbol).to_equal("GetStdHandle")
expect(result.i64_value).to_equal(wine_nt_bridge_stdout_handle())
```

</details>

#### existing bridge WriteFile still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_nt_bridge_dispatch_call("WriteFile", wine_nt_bridge_stdout_handle(), "hello", 5)
expect(result.ok).to_equal(true)
expect(result.symbol).to_equal("WriteFile")
expect(result.text_value).to_equal("hello")
```

</details>

#### existing bridge ExitProcess still works

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_nt_bridge_dispatch_call("ExitProcess", 0, "", 0)
expect(result.ok).to_equal(true)
expect(result.symbol).to_equal("ExitProcess")
expect(result.i64_value).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_nt_dispatch_table_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wine_nt_dispatch_table

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
