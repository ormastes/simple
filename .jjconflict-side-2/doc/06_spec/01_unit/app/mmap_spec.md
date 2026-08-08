# Mmap Specification

> <details>

<!-- sdn-diagram:id=mmap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mmap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mmap_spec -> std
mmap_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mmap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mmap Specification

## Scenarios

### MappedFile

#### struct construction

#### creates a valid MappedFile

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mf = MappedFile(address: 12345, size: 4096, path: "/tmp/test.txt")
expect(mf.is_valid()).to_equal(true)
expect(mf.file_size()).to_equal(4096)
expect(mf.path).to_equal("/tmp/test.txt")
```

</details>

#### zero address is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mf = MappedFile(address: 0, size: 0, path: "")
expect(mf.is_valid()).to_equal(false)
```

</details>

#### bounds checking

#### read_bytes rejects negative offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mf = MappedFile(address: 1000, size: 100, path: "test")
val result = mf.read_bytes(-1, 10)
expect(result.is_err()).to_equal(true)
```

</details>

#### read_bytes rejects negative length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mf = MappedFile(address: 1000, size: 100, path: "test")
val result = mf.read_bytes(0, -5)
expect(result.is_err()).to_equal(true)
```

</details>

#### read_bytes rejects read past end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mf = MappedFile(address: 1000, size: 100, path: "test")
val result = mf.read_bytes(90, 20)
expect(result.is_err()).to_equal(true)
```

</details>

#### read_string rejects negative offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mf = MappedFile(address: 1000, size: 100, path: "test")
val result = mf.read_string(-1, 10)
expect(result.is_err()).to_equal(true)
```

</details>

#### read_string rejects offset past end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mf = MappedFile(address: 1000, size: 100, path: "test")
val result = mf.read_string(200, 10)
expect(result.is_err()).to_equal(true)
```

</details>

#### close

#### invalidates mapping after close

1. var mf = MappedFile
   - Expected: mf.is_valid() is true
   - Expected: mf.is_valid() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mf = MappedFile(address: 1000, size: 100, path: "test")
expect(mf.is_valid()).to_equal(true)
# Note: close() calls rt_munmap which isn't available in interpreter
# We test the address zeroing logic by setting directly
mf.address = 0
mf.size = 0
expect(mf.is_valid()).to_equal(false)
```

</details>

#### open error handling

#### returns error for non-existent file

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = MappedFile.open("/tmp/simple_mmap_nonexistent_file_12345.txt")
expect(result.is_err()).to_equal(true)
val err = result.unwrap_err()
expect(err).to_contain("not found")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mmap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MappedFile

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
