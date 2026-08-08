# Nvfs 32bit Layout Specification

> <details>

<!-- sdn-diagram:id=nvfs_32bit_layout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvfs_32bit_layout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvfs_32bit_layout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvfs_32bit_layout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs 32bit Layout Specification

## Scenarios

### AC-3/R5 — NVFS superblock byte-equal across archs

#### x86_64 superblock dump exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(SUPERBLOCK_X86)).to_equal(true)
```

</details>

#### riscv32 superblock dump exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(SUPERBLOCK_RV32)).to_equal(true)
```

</details>

#### parity report exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(PARITY_REPORT)).to_equal(true)
```

</details>

#### parity report flags byte-equal = true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(PARITY_REPORT)
expect(r.contains("\"byte_equal\": true")).to_equal(true)
```

</details>

#### parity report records both file SHA-256 hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(PARITY_REPORT)
expect(r.contains("\"x86_64_sha256\"")).to_equal(true)
expect(r.contains("\"riscv32_sha256\"")).to_equal(true)
```

</details>

#### parity report shows identical SHA-256

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(PARITY_REPORT)
expect(r.contains("\"sha256_match\": true")).to_equal(true)
```

</details>

### AC-3/R5 — superblock layout is fixed-width 64-bit

#### superblock bytes are non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [u8] = file_read_bytes(SUPERBLOCK_X86)
expect(bytes.length() > 0).to_equal(true)
```

</details>

#### superblock bytes length is the locked fixed size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(PARITY_REPORT)
expect(r.contains("\"superblock_size_locked\": true")).to_equal(true)
```

</details>

### AC-3/R5 — 32-bit kernel rejects extents > 4 GiB

#### overflow report exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(OVERFLOW_REPORT)).to_equal(true)
```

</details>

#### riscv32 path returns PointerTooLarge for >4GiB extent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(OVERFLOW_REPORT)
expect(r.contains("\"riscv32_pointer_too_large\": true")).to_equal(true)
```

</details>

#### i686 path returns PointerTooLarge for >4GiB extent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(OVERFLOW_REPORT)
expect(r.contains("\"i686_pointer_too_large\": true")).to_equal(true)
```

</details>

#### armv7 path returns PointerTooLarge for >4GiB extent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(OVERFLOW_REPORT)
expect(r.contains("\"armv7_pointer_too_large\": true")).to_equal(true)
```

</details>

#### 64-bit archs accept >4GiB extents

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(OVERFLOW_REPORT)
expect(r.contains("\"x86_64_large_extent_ok\": true")).to_equal(true)
expect(r.contains("\"aarch64_large_extent_ok\": true")).to_equal(true)
expect(r.contains("\"riscv64_large_extent_ok\": true")).to_equal(true)
```

</details>

#### Result.Err path is taken — no panic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r: text = file_read(OVERFLOW_REPORT)
expect(r.contains("\"panicked\": false")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/multiarch/nvfs_32bit_layout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AC-3/R5 — NVFS superblock byte-equal across archs
- AC-3/R5 — superblock layout is fixed-width 64-bit
- AC-3/R5 — 32-bit kernel rejects extents > 4 GiB

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
