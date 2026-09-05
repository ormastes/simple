# fork_exec_spec

> Fork/Exec Structural Specification

<!-- sdn-diagram:id=fork_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fork_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fork_exec_spec -> std
fork_exec_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fork_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fork_exec_spec

Fork/Exec Structural Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/fork_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Fork/Exec Structural Specification

Tests the kernel-level exec (syscall 59) dispatch path structurally.
These specs verify:
  - exec rejects invalid arguments (empty path)
  - exec resolves executable bytes from synthetic sources
  - The resolution pipeline returns correct bytes end-to-end

No actual processes are spawned — all tests exercise the structural
contract of the executable resolution path.

Run:
  bin/simple test test/unit/os/kernel/loader/fork_exec_spec.spl

## Scenarios

### exec — argument validation
_Verify exec rejects invalid arguments at the structural level._

#### exec rejects empty path with EINVAL

1.  clear synthetic initramfs for test
2.  clear synthetic vfs for test
   - Expected: result.is_err() is true
   - Expected: result.err().unwrap().starts_with("EINVAL") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
val result = resolve_executable_bytes("", Architecture.X86_64)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap().starts_with("EINVAL")).to_equal(true)
```

</details>

#### exec rejects nonexistent path with ENOENT

1.  clear synthetic initramfs for test
2.  clear synthetic vfs for test
   - Expected: result.is_err() is true
   - Expected: result.err().unwrap().starts_with("ENOENT") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
# Non-absolute path avoids VFS reader (interpreter limitation)
val result = resolve_executable_bytes("no_such_binary", Architecture.X86_64)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap().starts_with("ENOENT")).to_equal(true)
```

</details>

### exec — image replacement structural
_Verify exec can load and parse a new image to replace the current one._

#### exec resolves synthetic bytes for a replacement image

1.  clear synthetic initramfs for test
2.  clear synthetic vfs for test
3.  set synthetic initramfs for test
   - Expected: bytes_result.is_ok() is true
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[1] equals `0x45.to_u8()`
4.  clear synthetic initramfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()

val payload = _elf_magic_payload()
_set_synthetic_initramfs_for_test("/sys/apps/new_image", payload)

# Step 1: resolve bytes (what exec does internally)
val bytes_result = resolve_executable_bytes("/sys/apps/new_image", Architecture.X86_64)
expect(bytes_result.is_ok()).to_equal(true)
val bytes = bytes_result.unwrap()
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[1]).to_equal(0x45.to_u8())

_clear_synthetic_initramfs_for_test()
```

</details>

#### exec resolves path bytes via resolve_executable_bytes_from_path_bytes

1.  clear synthetic initramfs for test
2.  clear synthetic vfs for test
3. app registry clear
4. app registry register
5.  set synthetic initramfs for test
   - Expected: result.is_ok() is true
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[1] equals `0x45.to_u8()`
6.  clear synthetic initramfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
app_registry_clear()
app_registry_register("/sys/apps/path_bytes_test", "PBTST.SMF", false)

val payload = _elf_magic_payload()
_set_synthetic_initramfs_for_test("/sys/apps/path_bytes_test", payload)

val path_bytes = rt_text_to_bytes("/sys/apps/path_bytes_test")
val result = resolve_executable_bytes_from_path_bytes(path_bytes, Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[1]).to_equal(0x45.to_u8())

_clear_synthetic_initramfs_for_test()
```

</details>

### fork+exec lifecycle — structural
_Verify the complete fork+exec API surface compiles and the pipeline is coherent._

#### full lifecycle: resolve -> ELF bytes confirmed

1.  clear synthetic initramfs for test
2.  clear synthetic vfs for test
3.  set synthetic initramfs for test
   - Expected: bytes_result.is_ok() is true
   - Expected: raw_bytes[0] equals `0x7F.to_u8()`
   - Expected: raw_bytes[1] equals `0x45.to_u8()`
   - Expected: raw_bytes[2] equals `0x4C.to_u8()`
   - Expected: raw_bytes[3] equals `0x46.to_u8()`
   - Expected: raw_bytes.len() equals `elf_data.len()`
4.  clear synthetic initramfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()

val elf_data = _minimal_elf64_x86_64()
_set_synthetic_initramfs_for_test("/sys/apps/lifecycle", elf_data)

# Parent would fork() (syscall 57) — returns child PID in parent.
# Child would exec() (syscall 59) — replaces its image.
# We test the exec resolution part structurally.

val bytes_result = resolve_executable_bytes("/sys/apps/lifecycle", Architecture.X86_64)
expect(bytes_result.is_ok()).to_equal(true)
val raw_bytes = bytes_result.unwrap()

# Verify resolved bytes are ELF
expect(raw_bytes[0]).to_equal(0x7F.to_u8())
expect(raw_bytes[1]).to_equal(0x45.to_u8())
expect(raw_bytes[2]).to_equal(0x4C.to_u8())
expect(raw_bytes[3]).to_equal(0x46.to_u8())

# Verify byte count matches
expect(raw_bytes.len()).to_equal(elf_data.len())

_clear_synthetic_initramfs_for_test()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
