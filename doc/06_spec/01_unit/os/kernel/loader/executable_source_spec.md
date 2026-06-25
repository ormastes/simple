# Executable Source Specification

> <details>

<!-- sdn-diagram:id=executable_source_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=executable_source_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

executable_source_spec -> std
executable_source_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=executable_source_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Executable Source Specification

## Scenarios

### executable source

#### resolves the canonical rv64 proof binary path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = resolve_executable_bytes(RV64_PROOF_BINARY_PATH, Architecture.Riscv64)
expect(result.is_ok()).to_equal(true)
val image = load_riscv_executable(result.unwrap(), Architecture.Riscv64)
expect(image.is_ok()).to_equal(true)
```

</details>

#### resolves rv64 bytes for known binaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = resolve_executable_bytes("/sys/services/vfs", Architecture.Riscv64)
expect(result.is_ok()).to_equal(true)
val image = load_riscv_executable(result.unwrap(), Architecture.Riscv64)
expect(image.is_ok()).to_equal(true)
```

</details>

#### resolves rv32 bytes for known binaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = resolve_executable_bytes("/sys/apps/desktop", Architecture.Riscv32)
expect(result.is_ok()).to_equal(true)
val image = load_riscv_executable(result.unwrap(), Architecture.Riscv32)
expect(image.is_ok()).to_equal(true)
```

</details>

#### resolves the canonical rv32 proof binary path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = resolve_executable_bytes(RV32_PROOF_BINARY_PATH, Architecture.Riscv32)
expect(result.is_ok()).to_equal(true)
val image = load_riscv_executable(result.unwrap(), Architecture.Riscv32)
expect(image.is_ok()).to_equal(true)
```

</details>

#### resolves x86_64 synthetic initramfs bytes by exact path

1.  clear synthetic initramfs for test
2. payload push
3. payload push
4. payload push
5. payload push
6.  set synthetic initramfs for test
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0x11.to_u8()`
   - Expected: bytes[3] equals `0x44.to_u8()`
7.  clear synthetic initramfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
var payload: [u8] = []
payload.push(0x11.to_u8())
payload.push(0x22.to_u8())
payload.push(0x33.to_u8())
payload.push(0x44.to_u8())
_set_synthetic_initramfs_for_test("/usr/bin/x86_exec_probe", payload)

val result = resolve_executable_bytes("/usr/bin/x86_exec_probe", Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x11.to_u8())
expect(bytes[3]).to_equal(0x44.to_u8())
_clear_synthetic_initramfs_for_test()
```

</details>

#### canonicalizes info path bytes through the VFS executable reader

1.  clear synthetic vfs for test
2. path bytes push
3. payload push
4. payload push
5. payload push
6. payload push
7. payload push
8.  set synthetic vfs file for test
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `5`
   - Expected: bytes[4] equals `0x10.to_u8()`
9.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_vfs_for_test()
var path_bytes: [u8] = []
for ch in "/sys/apps/info":
    path_bytes.push(ch.to_u8())
var payload: [u8] = []
payload.push(0x7F.to_u8())
payload.push(0x45.to_u8())
payload.push(0x4C.to_u8())
payload.push(0x46.to_u8())
payload.push(0x10.to_u8())
_set_synthetic_vfs_file_for_test("/sys/apps/info", payload)

val result = resolve_executable_bytes_from_path_bytes(path_bytes, Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(5)
expect(bytes[4]).to_equal(0x10.to_u8())
_clear_synthetic_vfs_for_test()
```

</details>

#### rejects unknown binary paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = resolve_executable_bytes("/sys/apps/missing", Architecture.Riscv64)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects unsupported host architectures

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = resolve_executable_bytes("/sys/services/vfs", Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/executable_source_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- executable source

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
