# dataset_vfs_spec

> @cover src/os/sosix/dataset_vfs.spl 80%

<!-- sdn-diagram:id=dataset_vfs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dataset_vfs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dataset_vfs_spec -> std
dataset_vfs_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dataset_vfs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dataset_vfs_spec

@cover src/os/sosix/dataset_vfs.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/dataset_vfs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/os/sosix/dataset_vfs.spl 80%

SOSIX Dataset-from-VFS Specification.

Tests that `sosix_dataset_create_from_file` correctly populates an immutable
sealed dataset from VFS bytes. The app-registry cache is used as the VFS
seeding mechanism — `g_vfs_read_file_bytes` consults it first, so no real
filesystem mount is required.

## Scenarios

### sosix_dataset_vfs_available

#### reports true after implementation lands

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(sosix_dataset_vfs_available()).to_equal(true)
```

</details>

### sosix_dataset_create_from_file argument validation

#### rejects an empty path

1. sosix share init
   - Expected: sosix_dataset_create_from_file("", 64u64) equals `0 - EINVAL as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
expect(sosix_dataset_create_from_file("", 64u64)).to_equal(0 - EINVAL as i64)
```

</details>

#### rejects zero max_bytes

1. sosix share init
   - Expected: sosix_dataset_create_from_file("/test/file.bin", 0u64) equals `0 - EINVAL as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
expect(sosix_dataset_create_from_file("/test/file.bin", 0u64)).to_equal(0 - EINVAL as i64)
```

</details>

#### rejects max_bytes exceeding SOSIX_DATASET_MAX_BYTES

1. sosix share init
   - Expected: sosix_dataset_create_from_file("/test/file.bin", SOSIX_DATASET_MAX_BYTES + 1) equals `0 - EINVAL as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
expect(sosix_dataset_create_from_file("/test/file.bin", SOSIX_DATASET_MAX_BYTES + 1)).to_equal(0 - EINVAL as i64)
```

</details>

### sosix_dataset_create_from_file missing file

#### returns ENOENT when the file is not in the VFS

1. sosix share init
2. app registry clear
   - Expected: sosix_dataset_create_from_file("/no/such/file.bin", 64u64) equals `0 - ENOENT as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
app_registry_clear()
expect(sosix_dataset_create_from_file("/no/such/file.bin", 64u64)).to_equal(0 - ENOENT as i64)
```

</details>

### sosix_dataset_create_from_file file-too-large

#### returns EFBIG when file bytes exceed max_bytes

1. sosix share init
2. app registry clear
3. app registry cache bytes
   - Expected: sosix_dataset_create_from_file("/test/big.bin", 3u64) equals `0 - EFBIG as i64`
4. app registry clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
app_registry_clear()
app_registry_cache_bytes("/test/big.bin", [1u8, 2u8, 3u8, 4u8, 5u8])
expect(sosix_dataset_create_from_file("/test/big.bin", 3u64)).to_equal(0 - EFBIG as i64)
app_registry_clear()
```

</details>

### sosix_dataset_create_from_file success path

#### creates a sealed dataset containing the file bytes

1. sosix share init
2. app registry clear
3. app registry cache bytes
   - Expected: sosix_dataset_is_sealed(handle as u64) is true
   - Expected: sosix_dataset_size(handle as u64) equals `5u64`
   - Expected: sosix_dataset_read_byte(handle as u64, 0u64) equals `72`
   - Expected: sosix_dataset_read_byte(handle as u64, 4u64) equals `111`
4. app registry clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
app_registry_clear()
app_registry_cache_bytes("/test/hello.bin", [72u8, 101u8, 108u8, 108u8, 111u8])
val handle = sosix_dataset_create_from_file("/test/hello.bin", 64u64)
expect(handle).to_be_greater_than(-1)
expect(sosix_dataset_is_sealed(handle as u64)).to_equal(true)
expect(sosix_dataset_size(handle as u64)).to_equal(5u64)
expect(sosix_dataset_read_byte(handle as u64, 0u64)).to_equal(72)
expect(sosix_dataset_read_byte(handle as u64, 4u64)).to_equal(111)
app_registry_clear()
```

</details>

#### creates a dataset matching exactly max_bytes when file fills the limit

1. sosix share init
2. app registry clear
3. app registry cache bytes
   - Expected: sosix_dataset_size(handle as u64) equals `3u64`
   - Expected: sosix_dataset_read_byte(handle as u64, 0u64) equals `0xAA`
   - Expected: sosix_dataset_read_byte(handle as u64, 2u64) equals `0xCC`
4. app registry clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
app_registry_clear()
app_registry_cache_bytes("/test/exact.bin", [0xAAu8, 0xBBu8, 0xCCu8])
val handle = sosix_dataset_create_from_file("/test/exact.bin", 3u64)
expect(handle).to_be_greater_than(-1)
expect(sosix_dataset_size(handle as u64)).to_equal(3u64)
expect(sosix_dataset_read_byte(handle as u64, 0u64)).to_equal(0xAA)
expect(sosix_dataset_read_byte(handle as u64, 2u64)).to_equal(0xCC)
app_registry_clear()
```

</details>

#### returns independent handles for different paths

1. sosix share init
2. app registry clear
3. app registry cache bytes
4. app registry cache bytes
   - Expected: sosix_dataset_size(ha as u64) equals `2u64`
   - Expected: sosix_dataset_size(hb as u64) equals `3u64`
   - Expected: sosix_dataset_read_byte(hb as u64, 0u64) equals `9`
5. app registry clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sosix_share_init()
app_registry_clear()
app_registry_cache_bytes("/test/a.bin", [1u8, 2u8])
app_registry_cache_bytes("/test/b.bin", [9u8, 8u8, 7u8])
val ha = sosix_dataset_create_from_file("/test/a.bin", 64u64)
val hb = sosix_dataset_create_from_file("/test/b.bin", 64u64)
expect(ha).to_be_greater_than(-1)
expect(hb).to_be_greater_than(-1)
expect(ha).to_not_equal(hb)
expect(sosix_dataset_size(ha as u64)).to_equal(2u64)
expect(sosix_dataset_size(hb as u64)).to_equal(3u64)
expect(sosix_dataset_read_byte(hb as u64, 0u64)).to_equal(9)
app_registry_clear()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
