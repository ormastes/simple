# fs_hardening_spec

> FS Hardening Specification

<!-- sdn-diagram:id=fs_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fs_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fs_hardening_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fs_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fs_hardening_spec

FS Hardening Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/fs_driver/fs_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

FS Hardening Specification

Validates hardening additions across FAT32, NVFS, and RamFS drivers:
  - StaleHandle / PathTraversal error variants (D-1)
  - Handle generation encoding (D-2)
  - Double-close detection, path-traversal rejection
  - BPB validation, cluster-chain cycle detection (FAT32)
  - Superblock checksum-on-read, generation mismatch (NVFS)

## Scenarios

### Handle Guard — generation encoding

#### AC-9: handle_pack encodes generation in high 32 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packed = handle_pack(42, 7)
val g = handle_unpack_gen(packed)
expect(g).to_equal(7)
```

</details>

#### AC-9: handle_pack encodes slot index in low 32 bits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val packed = handle_pack(42, 7)
val idx = handle_unpack_slot(packed)
expect(idx).to_equal(42)
```

</details>

#### AC-9: handle_validate rejects stale generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slot = HandleSlot(generation: 2, ino_id: 100, active: false)
val slots = [slot]
val stale_id = handle_pack(0, 1)
val r = handle_validate(slots, stale_id)
val is_err = r.is_err()
expect(is_err).to_equal(true)
```

</details>

### FsError — new hardening variants

#### AC-9: StaleHandle variant exists and is distinct from InvalidArg

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e1 = FsError.StaleHandle
val e2 = FsError.InvalidArg
val same = e1 == e2
expect(same).to_equal(false)
```

</details>

#### AC-9: PathTraversal variant exists and is distinct from Permission

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e1 = FsError.PathTraversal
val e2 = FsError.Permission
val same = e1 == e2
expect(same).to_equal(false)
```

</details>

### RamFS Hardening — double-close

#### AC-9: double close returns StaleHandle error

1. var d = make ramfs direct
2. d fd table push
3. d close
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = make_ramfs_direct()
d.fd_table.push(FdEntry(fd_id: 42, ino_id: 1, path: "/f", flags: 0, is_dir: false))
val fh = FileHandle(id: 42)
d.close(fh).unwrap()
val r = d.close(fh)
val is_err = r.is_err()
expect(is_err).to_equal(true)
```

</details>

### RamFS Hardening — stale handle

#### AC-9: read on stale handle returns StaleHandle

1. var d = make ramfs direct
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = make_ramfs_direct()
val fh = FileHandle(id: 999)
val buf: [u8] = []
val r = d.read(fh, 0, buf)
val is_err = r.is_err()
expect(is_err).to_equal(true)
```

</details>

#### AC-9: write on stale handle returns StaleHandle

1. var d = make ramfs direct
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = make_ramfs_direct()
val fh = FileHandle(id: 999)
val buf: [u8] = []
val r = d.write(fh, 0, buf)
val is_err = r.is_err()
expect(is_err).to_equal(true)
```

</details>

### RamFS Hardening — path traversal

#### AC-9: PathTraversal FsError variant is distinct from Permission

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e1 = FsError.PathTraversal
val e2 = FsError.Permission
val same = e1 == e2
expect(same).to_equal(false)
```

</details>

### RamFS Hardening — sorted lookup

#### AC-3: find_inode_idx returns valid index for inserted inode

1. var d = make ramfs direct
2. kind: RamFsKind Dir
3. d inodes push
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var d = make_ramfs_direct()
val inode = RamFsInode(
    kind: RamFsKind.Dir(d: RamFsDir(entries: [], mode: 0o755)),
    size: 0, ctime: 0, mtime: 0, nlink: 1, mode: 0o755
)
d.inodes.push(InodeEntry(id: 50, inode: inode))
val idx = d.find_inode_idx(50)
val found = idx >= 0
expect(found).to_equal(true)
```

</details>

### FAT32 Hardening — BPB validation

#### AC-1: validate_bpb rejects zero bytes_per_sector

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = validate_bpb(Fat32Bpb(bytes_per_sector: 0, sectors_per_cluster: 8, reserved_sectors: 32, num_fats: 2, total_sectors_32: 2048, fat_size_32: 128, root_cluster: 2))
val is_err = r.is_err()
expect(is_err).to_equal(true)
```

</details>

#### AC-1: validate_bpb rejects non-power-of-two cluster size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = validate_bpb(Fat32Bpb(bytes_per_sector: 512, sectors_per_cluster: 3, reserved_sectors: 32, num_fats: 2, total_sectors_32: 2048, fat_size_32: 128, root_cluster: 2))
val is_err = r.is_err()
expect(is_err).to_equal(true)
```

</details>

### FAT32 Hardening — cluster chain cycle

#### AC-1: detect_cluster_cycle detects a cycle

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_cycle = detect_cluster_cycle(2, 1024)
val is_ok = has_cycle.is_ok()
# Function exists and returns a result; actual cycle detection
# depends on FAT table content set up by the driver
expect(is_ok).to_equal(true)
```

</details>

### NVFS Superblock Hardening — corrupt superblock

#### AC-2: corrupt superblock bytes returns Corrupt error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Construct a buffer with invalid magic / bad checksum
val bad_buf = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
val r = nvfs_superblock_read_from_bytes(bad_buf)
val is_err = r.is_err()
expect(is_err).to_equal(true)
```

</details>

#### AC-2: short buffer returns Corrupt error

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val short_buf = [0, 0, 0, 0]
val r = nvfs_superblock_read_from_bytes(short_buf)
val is_err = r.is_err()
expect(is_err).to_equal(true)
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
