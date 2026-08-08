# Executable Source Vfs Specification

> _Phase 4 coverage: initramfs-first resolution and legacy stub fallback._

<!-- sdn-diagram:id=executable_source_vfs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=executable_source_vfs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

executable_source_vfs_spec -> std
executable_source_vfs_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=executable_source_vfs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Executable Source Vfs Specification

## Scenarios

### executable source — VFS-backed loading
_Phase 4 coverage: initramfs-first resolution and legacy stub fallback._

#### returns ENOENT for unknown paths

1.  clear synthetic initramfs for test
   - Expected: result.is_err() is true
   - Expected: result.err().unwrap().starts_with("ENOENT") is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
val result = resolve_executable_bytes("nonexistent", Architecture.Riscv64)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap().starts_with("ENOENT")).to_equal(true)
```

</details>

#### returns EINVAL for an empty path

1.  clear synthetic initramfs for test
   - Expected: result.is_err() is true
   - Expected: result.err().unwrap().starts_with("EINVAL") is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
val result = resolve_executable_bytes("", Architecture.Riscv64)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap().starts_with("EINVAL")).to_equal(true)
```

</details>

#### resolves proof binary path via initramfs synthetic

1.  clear synthetic initramfs for test

2.  clear synthetic vfs for test

3.  set synthetic initramfs for test
   - Expected: result.is_ok() is true
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[1] equals `0x45.to_u8()`

4.  clear synthetic initramfs for test

5.  clear synthetic vfs for test


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
val payload = _elf_magic_payload()
_set_synthetic_initramfs_for_test(RV64_PROOF_BINARY_PATH, payload)
val result = resolve_executable_bytes(RV64_PROOF_BINARY_PATH, Architecture.Riscv64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[1]).to_equal(0x45.to_u8())
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
```

</details>

#### resolves a synthetic initramfs entry by exact path

1.  clear synthetic initramfs for test

2.  clear synthetic vfs for test

3. payload push

4. payload push

5. payload push

6. payload push

7.  set synthetic initramfs for test
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0xDE.to_u8()`
   - Expected: bytes[3] equals `0xEF.to_u8()`

8.  clear synthetic initramfs for test

9.  clear synthetic vfs for test


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
var payload: [u8] = []
payload.push(0xDE.to_u8())
payload.push(0xAD.to_u8())
payload.push(0xBE.to_u8())
payload.push(0xEF.to_u8())
_set_synthetic_initramfs_for_test("/usr/bin/foo", payload)

val result = resolve_executable_bytes("/usr/bin/foo", Architecture.Riscv64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0xDE.to_u8())
expect(bytes[3]).to_equal(0xEF.to_u8())
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
```

</details>

#### falls back to VFS bytes when initramfs has no matching executable

1.  clear synthetic initramfs for test

2.  clear synthetic vfs for test

3.  set synthetic vfs file for test
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[3] equals `0x46.to_u8()`

4.  clear synthetic vfs for test


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
val payload = _elf_magic_payload()
_set_synthetic_vfs_file_for_test("/sys/apps/hello_world", payload)

val result = resolve_executable_bytes("/sys/apps/hello_world", Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[3]).to_equal(0x46.to_u8())
_clear_synthetic_vfs_for_test()
```

</details>

#### falls back to VFS bytes for arbitrary executable paths

1.  clear synthetic initramfs for test

2.  clear synthetic vfs for test

3.  set synthetic vfs file for test
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[3] equals `0x46.to_u8()`

4.  clear synthetic vfs for test


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
val payload = _elf_magic_payload()
_set_synthetic_vfs_file_for_test("/home/RUNME.ELF", payload)

val result = resolve_executable_bytes("/home/RUNME.ELF", Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[3]).to_equal(0x46.to_u8())
_clear_synthetic_vfs_for_test()
```

</details>

#### falls back to seeded FAT32 aliases for smux

1.  clear synthetic initramfs for test

2.  clear synthetic vfs for test

3. app registry load hardcoded fallback

4.  set synthetic vfs file for test
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[3] equals `0x46.to_u8()`

5.  clear synthetic vfs for test

6. app registry clear


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
app_registry_load_hardcoded_fallback()
val payload = _elf_magic_payload()
_set_synthetic_vfs_file_for_test("/SYS/APPS/SMUXSMF.SMF", payload)

val result = resolve_executable_bytes("/sys/apps/smux", Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[3]).to_equal(0x46.to_u8())
_clear_synthetic_vfs_for_test()
app_registry_clear()
```

</details>

#### falls back to seeded FAT32 short-name aliases for desktop apps

1.  clear synthetic initramfs for test

2.  clear synthetic vfs for test

3. app registry load hardcoded fallback

4.  set synthetic vfs file for test
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[3] equals `0x46.to_u8()`

5.  clear synthetic vfs for test

6. app registry clear


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
app_registry_load_hardcoded_fallback()
val payload = _elf_magic_payload()
_set_synthetic_vfs_file_for_test("/SYS/APPS/BROWSMF.SMF", payload)

val result = resolve_executable_bytes("/sys/apps/browser_demo", Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[3]).to_equal(0x46.to_u8())
_clear_synthetic_vfs_for_test()
app_registry_clear()
```

</details>

#### resolves seeded desktop app bytes without dynamic path text reconstruction

1.  clear synthetic initramfs for test

2.  clear synthetic vfs for test

3. app registry load hardcoded fallback

4.  set synthetic vfs file for test
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[3] equals `0x46.to_u8()`

5.  clear synthetic vfs for test

6. app registry clear


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
app_registry_load_hardcoded_fallback()
val payload = _elf_magic_payload()
_set_synthetic_vfs_file_for_test("/SYS/APPS/BROWSMF.SMF", payload)

val result = resolve_executable_bytes_from_path_bytes("/sys/apps/browser_demo".bytes(), Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[3]).to_equal(0x46.to_u8())
_clear_synthetic_vfs_for_test()
app_registry_clear()
```

</details>

#### falls back to root-level aliases on seeded disk images

1.  clear synthetic initramfs for test

2.  clear synthetic vfs for test

3. app registry load hardcoded fallback

4.  set synthetic vfs file for test
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[3] equals `0x46.to_u8()`

5.  clear synthetic vfs for test

6. app registry clear


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
app_registry_load_hardcoded_fallback()
val payload = _elf_magic_payload()
_set_synthetic_vfs_file_for_test("/BROWSMF.SMF", payload)

val result = resolve_executable_bytes("/sys/apps/browser_demo", Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[3]).to_equal(0x46.to_u8())
_clear_synthetic_vfs_for_test()
app_registry_clear()
```

</details>

#### falls back to root-level SMF aliases on seeded disk images

1.  clear synthetic initramfs for test

2.  clear synthetic vfs for test

3. app registry load hardcoded fallback

4.  set synthetic vfs file for test
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `132`
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[3] equals `0x46.to_u8()`
   - Expected: bytes[4] equals `0x53.to_u8()`

5.  clear synthetic vfs for test

6. app registry clear


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
app_registry_load_hardcoded_fallback()
val payload = _exec_smf_payload(_elf_magic_payload())
_set_synthetic_vfs_file_for_test("/BROWSMF.SMF", payload)

val result = resolve_executable_bytes("/sys/apps/browser_demo.smf", Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(132)
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[3]).to_equal(0x46.to_u8())
expect(bytes[4]).to_equal(0x53.to_u8())
_clear_synthetic_vfs_for_test()
app_registry_clear()
```

</details>

#### resolved executable byte count matches injected payload

1.  clear synthetic initramfs for test

2.  clear synthetic vfs for test

3. app registry clear

4.  set synthetic initramfs for test
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `17`
   - Expected: bytes[0] equals `0x7F.to_u8()`

5.  clear synthetic initramfs for test

6.  clear synthetic vfs for test


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
app_registry_clear()
val payload = _make_17_byte_payload()
_set_synthetic_initramfs_for_test("/usr/bin/bar", payload)

val result = resolve_executable_bytes("/usr/bin/bar", Architecture.Riscv64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(17)
expect(bytes[0]).to_equal(0x7F.to_u8())
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
```

</details>

#### proof binary paths are defined for boot-test fallback

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RV64_PROOF_BINARY_PATH).to_equal("/sys/apps/rv64_user_proof")
expect(RV32_PROOF_BINARY_PATH).to_equal("/sys/apps/rv32_user_proof")
```

</details>

#### unregistered paths without a synthetic entry fall through to ENOENT

1.  clear synthetic initramfs for test
   - Expected: result.is_err() is true
   - Expected: result.err().unwrap().starts_with("ENOENT") is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
val result = resolve_executable_bytes("usr/bin/clang", Architecture.Riscv64)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap().starts_with("ENOENT")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/executable_source_vfs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- executable source — VFS-backed loading

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
