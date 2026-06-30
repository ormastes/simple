# ELF magic

> Spawn Pipeline End-to-End Specification

<!-- sdn-diagram:id=spawn_pipeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spawn_pipeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spawn_pipeline_spec -> std
spawn_pipeline_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spawn_pipeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ELF magic

Spawn Pipeline End-to-End Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/spawn_pipeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Spawn Pipeline End-to-End Specification

Proves the full executable loading pipeline: path resolution -> byte loading ->
ELF parsing -> image building. Each test exercises a real production function
from the loader subsystem using synthetic test injection hooks so that no actual
VFS or initramfs is required.

Run:
  bin/simple test test/unit/os/kernel/loader/spawn_pipeline_spec.spl

## Scenarios

### spawn pipeline — executable resolution
_resolve_executable_bytes returns bytes for registered and unregistered paths._

#### resolves bytes for a path injected via synthetic initramfs

1.  clear synthetic initramfs for test
2.  clear synthetic vfs for test
3.  set synthetic initramfs for test
   - Expected: result.is_ok() is true
   - Expected: bytes.len() equals `payload.len()`
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[1] equals `0x45.to_u8()`
   - Expected: bytes[2] equals `0x4C.to_u8()`
   - Expected: bytes[3] equals `0x46.to_u8()`
4.  clear synthetic initramfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
val payload = _elf_magic_payload()
_set_synthetic_initramfs_for_test("/sys/apps/test_hello", payload)
val result = resolve_executable_bytes("/sys/apps/test_hello", Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes.len()).to_equal(payload.len())
# Verify ELF magic preserved
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[1]).to_equal(0x45.to_u8())
expect(bytes[2]).to_equal(0x4C.to_u8())
expect(bytes[3]).to_equal(0x46.to_u8())
_clear_synthetic_initramfs_for_test()
```

</details>

#### resolves bytes for an unregistered arbitrary path via synthetic VFS

1.  clear synthetic initramfs for test
2.  clear synthetic vfs for test
3.  set synthetic vfs file for test
   - Expected: result.is_ok() is true
   - Expected: bytes[0] equals `0x7F.to_u8()`
4.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
val payload = _elf_magic_payload()
_set_synthetic_vfs_file_for_test("/usr/local/bin/custom_tool", payload)
val result = resolve_executable_bytes("/usr/local/bin/custom_tool", Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes[0]).to_equal(0x7F.to_u8())
_clear_synthetic_vfs_for_test()
```

</details>

#### returns ENOENT for a path not present in any source

1.  clear synthetic initramfs for test
2.  clear synthetic vfs for test
   - Expected: result.is_err() is true
   - Expected: result.err().unwrap().starts_with("ENOENT") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
# Use a non-absolute path to avoid hitting the VFS reader which
# cannot be resolved in interpreter mode.
val result = resolve_executable_bytes("nonexistent", Architecture.X86_64)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap().starts_with("ENOENT")).to_equal(true)
```

</details>

#### returns the correct byte count via resolve_executable_size

1.  clear synthetic initramfs for test
2.  clear synthetic vfs for test
3.  set synthetic initramfs for test
   - Expected: size_result.is_ok() is true
   - Expected: size_result.unwrap() equals `payload.len().to_u64()`
4.  clear synthetic initramfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
val payload = _elf_magic_payload()
_set_synthetic_initramfs_for_test("/sys/apps/size_check", payload)
val size_result = resolve_executable_size("/sys/apps/size_check", Architecture.X86_64)
expect(size_result.is_ok()).to_equal(true)
expect(size_result.unwrap()).to_equal(payload.len().to_u64())
_clear_synthetic_initramfs_for_test()
```

</details>

### spawn pipeline — ELF parser validation
_ELF parser validates magic bytes and rejects non-ELF data._

#### rejects non-ELF data with an error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_data = _non_elf_payload()
val result = load_user_executable(bad_data, Architecture.X86_64)
expect(result.is_err()).to_equal(true)
val err_msg = result.err().unwrap()
expect(err_msg.len() > 0).to_equal(true)
```

</details>

#### rejects truncated ELF data (magic only, no headers)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val truncated = _elf_magic_only_payload()
val result = load_user_executable(truncated, Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

### spawn pipeline — process image builder
_build_user_process_image rejects invalid data._

#### rejects non-ELF data

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_data = _non_elf_payload()
val result = build_user_process_image(
    "/sys/apps/bad",
    bad_data,
    Architecture.X86_64,
    [],
    []
)
expect(result.is_err()).to_equal(true)
```

</details>

### spawn pipeline — argv marshaling
_sosix_marshal_string_vector produces correct byte layout._

#### marshals a single-element argv into NUL-terminated bytes with offset table

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _marshal_string_vector(["hello"])
# "hello" = 5 bytes + NUL = 6 string bytes
# offset table: 1 entry (8 bytes) + NULL terminator (8 bytes) = 16 bytes
# total = 6 + 16 = 22 bytes
expect(buf.len()).to_equal(22)
# First string starts at offset 0
expect(buf[0]).to_equal(0x68.to_u8())  # 'h'
expect(buf[1]).to_equal(0x65.to_u8())  # 'e'
expect(buf[5]).to_equal(0.to_u8())      # NUL
```

</details>

#### marshals multiple argv entries with correct offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _marshal_string_vector(["ab", "cd"])
# "ab\0" = 3 bytes at offset 0, "cd\0" = 3 bytes at offset 3
# offset table: 2 entries (16 bytes) + NULL (8 bytes) = 24 bytes
# total = 6 + 24 = 30 bytes
expect(buf.len()).to_equal(30)
# First string "ab"
expect(buf[0]).to_equal(0x61.to_u8())  # 'a'
expect(buf[1]).to_equal(0x62.to_u8())  # 'b'
expect(buf[2]).to_equal(0.to_u8())      # NUL
# Second string "cd"
expect(buf[3]).to_equal(0x63.to_u8())  # 'c'
expect(buf[4]).to_equal(0x64.to_u8())  # 'd'
expect(buf[5]).to_equal(0.to_u8())      # NUL
# First offset entry = 0 (LE u64)
expect(buf[6]).to_equal(0.to_u8())
# Second offset entry = 3 (LE u64)
expect(buf[14]).to_equal(3.to_u8())
```

</details>

#### returns empty buffer for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _marshal_string_vector([])
expect(buf.len()).to_equal(0)
```

</details>

### spawn pipeline — app registry
_app_registry_lookup and app_registry_fat32_alias resolve entries._

#### looks up a registered entry by canonical path

1. app registry clear
2. app registry load
   - Expected: entry != nil is true
   - Expected: e.canonical_path equals `/sys/apps/test_hello`
   - Expected: e.fat32_leaf equals `TESTHLO.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val entry = app_registry_lookup("/sys/apps/test_hello")
expect(entry != nil).to_equal(true)
val e = entry.unwrap()
expect(e.canonical_path).to_equal("/sys/apps/test_hello")
expect(e.fat32_leaf).to_equal("TESTHLO.SMF")
```

</details>

#### returns FAT32 alias for registered app

1. app registry clear
2. app registry load
   - Expected: alias != nil is true
   - Expected: alias.unwrap() equals `/SYS/APPS/TESTHLO.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
val alias = app_registry_fat32_alias("/sys/apps/test_hello")
expect(alias != nil).to_equal(true)
expect(alias.unwrap()).to_equal("/SYS/APPS/TESTHLO.SMF")
```

</details>

#### returns nil for unregistered path

1. app registry clear
2. app registry load
   - Expected: app_registry_lookup("/sys/apps/nonexistent") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_load(_test_manifest())
expect(app_registry_lookup("/sys/apps/nonexistent")).to_equal(nil)
```

</details>

#### finds dynamically registered entries

1. app registry clear
2. app registry register
   - Expected: entry != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
app_registry_clear()
app_registry_register("/sys/apps/dynamic_tool", "DYNTOOL.SMF", false)
val entry = app_registry_lookup("/sys/apps/dynamic_tool")
expect(entry != nil).to_equal(true)
```

</details>

### spawn pipeline — full pipeline integration
_End-to-end: path -> bytes -> ELF parse -> image build._

#### resolves a synthetic path and verifies ELF magic in resolved bytes

1.  clear synthetic initramfs for test
2.  clear synthetic vfs for test
3. app registry clear
4. app registry register
5.  set synthetic initramfs for test
   - Expected: resolve_result.is_ok() is true
   - Expected: raw_bytes[0] equals `0x7F.to_u8()`
   - Expected: raw_bytes[1] equals `0x45.to_u8()`
   - Expected: raw_bytes[2] equals `0x4C.to_u8()`
   - Expected: raw_bytes[3] equals `0x46.to_u8()`
   - Expected: raw_bytes.len() equals `elf_data.len()`
6.  clear synthetic initramfs for test
7.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
app_registry_clear()
app_registry_register("/sys/apps/e2e_test", "E2ETEST.SMF", false)

val elf_data = _minimal_elf64_x86_64()
_set_synthetic_initramfs_for_test("/sys/apps/e2e_test", elf_data)

# Resolve path to bytes
val resolve_result = resolve_executable_bytes("/sys/apps/e2e_test", Architecture.X86_64)
expect(resolve_result.is_ok()).to_equal(true)
val raw_bytes = resolve_result.unwrap()

# Verify the resolved bytes have ELF magic
expect(raw_bytes[0]).to_equal(0x7F.to_u8())
expect(raw_bytes[1]).to_equal(0x45.to_u8())
expect(raw_bytes[2]).to_equal(0x4C.to_u8())
expect(raw_bytes[3]).to_equal(0x46.to_u8())

# Verify resolved byte count matches injected payload
expect(raw_bytes.len()).to_equal(elf_data.len())

_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
```

</details>

#### fails gracefully when the resolved bytes are not valid ELF

1.  clear synthetic initramfs for test
2.  clear synthetic vfs for test
3.  set synthetic initramfs for test
   - Expected: resolve_result.is_ok() is true
4. resolve result unwrap
   - Expected: image_result.is_err() is true
5.  clear synthetic initramfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()

val bad_data = _non_elf_payload()
_set_synthetic_initramfs_for_test("/sys/apps/bad_binary", bad_data)

val resolve_result = resolve_executable_bytes("/sys/apps/bad_binary", Architecture.X86_64)
expect(resolve_result.is_ok()).to_equal(true)

val image_result = build_user_process_image(
    "/sys/apps/bad_binary",
    resolve_result.unwrap(),
    Architecture.X86_64,
    [],
    []
)
expect(image_result.is_err()).to_equal(true)

_clear_synthetic_initramfs_for_test()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
