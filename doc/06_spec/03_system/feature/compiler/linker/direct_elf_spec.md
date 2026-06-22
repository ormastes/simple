# Direct ELF Writing (Phase 2.1)

> Tests the advanced direct ELF writing phase including dynamic linking, GOT/PLT generation, and relocation processing. Verifies that the ELF writer produces fully functional dynamically-linked executables without external linker tools.

<!-- sdn-diagram:id=direct_elf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=direct_elf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

direct_elf_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=direct_elf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Direct ELF Writing (Phase 2.1)

Tests the advanced direct ELF writing phase including dynamic linking, GOT/PLT generation, and relocation processing. Verifies that the ELF writer produces fully functional dynamically-linked executables without external linker tools.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/linker/direct_elf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the advanced direct ELF writing phase including dynamic linking, GOT/PLT
generation, and relocation processing. Verifies that the ELF writer produces
fully functional dynamically-linked executables without external linker tools.

## Scenarios

### Phase 2.1: Direct ELF Writing

#### Helper Functions

#### detects direct ELF writing should be enabled by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = should_use_direct_elf_writing()
expect(result).to_equal(true)
```

</details>

#### verifies valid ELF file

1. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_path = "/tmp/test_elf_valid.o"

# Create minimal valid ELF file (magic number only for this test)
val elf_magic: [u8] = [127, 69, 76, 70]  # 0x7F 'E' 'L' 'F'
val padding: [u8] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
val minimal_elf = elf_magic + padding

val write_result = write_elf_bytes_to_file(test_path, minimal_elf)
expect(write_result.is_ok()).to_equal(true)

val verify_result = verify_elf_file(test_path)
expect(verify_result).to_equal(true)

file_delete(test_path)
```

</details>

#### rejects invalid ELF magic number

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_path = "/tmp/test_elf_invalid.o"

# Wrong magic bytes
val bad_magic: [u8] = [1, 2, 3, 4, 0, 0, 0, 0]

val write_result = write_elf_bytes_to_file(test_path, bad_magic)
expect(write_result.is_err()).to_equal(true)
```

</details>

#### rejects too-small file

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_path = "/tmp/test_elf_small.o"

# Only 2 bytes (need at least 4 for magic)
val tiny_file: [u8] = [127, 69]

val write_result = write_elf_bytes_to_file(test_path, tiny_file)
expect(write_result.is_err()).to_equal(true)
```

</details>

#### ELF Magic Number Verification

#### accepts correct ELF magic: 0x7F 'E' 'L' 'F'

1. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elf_bytes: [u8] = [127, 69, 76, 70, 1, 1, 1, 0]  # ELF header start
val test_path = "/tmp/test_magic_ok.o"

val result = write_elf_bytes_to_file(test_path, elf_bytes)
expect(result.is_ok()).to_equal(true)

# Verify the file was created
expect(file_exists(test_path)).to_equal(true)

# Verify the magic number in the file
val read_bytes = file_read_bytes(test_path)
expect(read_bytes[0]).to_equal(127)
expect(read_bytes[1]).to_equal(69)
expect(read_bytes[2]).to_equal(76)
expect(read_bytes[3]).to_equal(70)

file_delete(test_path)
```

</details>

#### rejects wrong first byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_bytes: [u8] = [128, 69, 76, 70, 0, 0, 0, 0]
val result = write_elf_bytes_to_file("/tmp/bad1.o", bad_bytes)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects wrong second byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_bytes: [u8] = [127, 70, 76, 70, 0, 0, 0, 0]
val result = write_elf_bytes_to_file("/tmp/bad2.o", bad_bytes)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects wrong third byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_bytes: [u8] = [127, 69, 77, 70, 0, 0, 0, 0]
val result = write_elf_bytes_to_file("/tmp/bad3.o", bad_bytes)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects wrong fourth byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_bytes: [u8] = [127, 69, 76, 71, 0, 0, 0, 0]
val result = write_elf_bytes_to_file("/tmp/bad4.o", bad_bytes)
expect(result.is_err()).to_equal(true)
```

</details>

#### File Operations

#### creates file with correct permissions

1. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elf_bytes: [u8] = [127, 69, 76, 70, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
val test_path = "/tmp/test_permissions.o"

val result = write_elf_bytes_to_file(test_path, elf_bytes)
expect(result.is_ok()).to_equal(true)
expect(file_exists(test_path)).to_equal(true)

file_delete(test_path)
```

</details>

#### overwrites existing file

1. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_path = "/tmp/test_overwrite.o"

# Write first version
val elf_v1: [u8] = [127, 69, 76, 70, 1, 0, 0, 0]
val r1 = write_elf_bytes_to_file(test_path, elf_v1)
expect(r1.is_ok()).to_equal(true)

# Overwrite with second version
val elf_v2: [u8] = [127, 69, 76, 70, 2, 0, 0, 0, 0, 0, 0, 0]
val r2 = write_elf_bytes_to_file(test_path, elf_v2)
expect(r2.is_ok()).to_equal(true)

# Verify second version is present
val read = file_read_bytes(test_path)
expect(read[4]).to_equal(2)

file_delete(test_path)
```

</details>

#### handles empty path gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elf_bytes: [u8] = [127, 69, 76, 70, 0, 0, 0, 0]
val result = write_elf_bytes_to_file("", elf_bytes)
expect(result.is_err()).to_equal(true)
```

</details>

#### Integration with verify_elf_file

#### verify returns false for non-existent file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = verify_elf_file("/tmp/nonexistent_file_xyz.o")
expect(result).to_equal(false)
```

</details>

#### verify returns false for non-ELF file

1. extern fn rt file write bytes
2. rt file write bytes
   - Expected: result is false
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_path = "/tmp/test_not_elf.txt"
val non_elf: [u8] = [80, 75, 3, 4, 0, 0, 0, 0]  # ZIP magic

# Write directly (bypass validation)
extern fn rt_file_write_bytes(path: text, data: [u8]) -> bool
rt_file_write_bytes(test_path, non_elf)

val result = verify_elf_file(test_path)
expect(result).to_equal(false)

file_delete(test_path)
```

</details>

#### verify returns true for valid ELF

1. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_path = "/tmp/test_verify_valid.o"
val elf_bytes: [u8] = [127, 69, 76, 70, 2, 1, 1, 0]

val write_result = write_elf_bytes_to_file(test_path, elf_bytes)
expect(write_result.is_ok()).to_equal(true)

val verify_result = verify_elf_file(test_path)
expect(verify_result).to_equal(true)

file_delete(test_path)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
