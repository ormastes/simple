# FAT32 Dirent Persistence — Wave-4e Spec

> Verifies that after write():

<!-- sdn-diagram:id=fat32_dirent_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fat32_dirent_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fat32_dirent_spec -> std
fat32_dirent_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fat32_dirent_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FAT32 Dirent Persistence — Wave-4e Spec

Verifies that after write():

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/fs/fat32_dirent_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

**Bug:** fat32_no_cycle_guard_chain_walk_2026-06-11  FINDING-T2-dirent
Verifies that after write():
  1. open() records dirent_sector and dirent_offset in the returned FileHandle.
  2. write() calls _update_dirent; re-reading the root-dir sector shows
     first_cluster hi/lo (offsets +20..+21, +26..+27) and file_size u32
     (offsets +28..+31) updated correctly in the on-disk dirent.
  3. root_dir_data cache is updated coherently (stat() sees the new size).
  4. A second write() (append) correctly accumulates file_size in the dirent.
  5. dirent_sector=0 handle skips _update_dirent without error.

Geometry used throughout:
  fat_start=32, data_start=64, bps=512, spc=1, data_clusters=8.
  root_cluster=2 → root dir LBA = 64 + (2-2) = 64.
  FAT entry for cluster N: 4-byte little-endian at LBA 32 byte-offset N*4.
  The single 8.3 dirent for "TEST    TXT" is placed at byte offset 0 of LBA 64.
  So dirent_sector=64, dirent_offset=0.

## Scenarios

### fat32 dirent persistence — wave-4e

### open() records dirent location

#### dirent_sector equals root-dir LBA (64) for entry at byte 32

- assert true
   - Expected: h.dirent_sector equals `64u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root_dir = _make_root_dir_with_test_txt()
val fs = _make_fs_with_rootdir(root_dir)
val h_result = fs.open("/TEST.TXT")
assert_true(h_result.is_ok())
val h = h_result.unwrap()
# Entry is in the root-dir sector (LBA 64); offset 32 < 512 so same sector.
expect(h.dirent_sector).to_equal(64u64)
```

</details>

#### dirent_offset equals 32 for the second directory slot

- assert true
   - Expected: h.dirent_offset equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root_dir = _make_root_dir_with_test_txt()
val fs = _make_fs_with_rootdir(root_dir)
val h_result = fs.open("/TEST.TXT")
assert_true(h_result.is_ok())
val h = h_result.unwrap()
expect(h.dirent_offset).to_equal(32)
```

</details>

### write() persists first_cluster and file_size to on-disk dirent

#### after write, dirent first_cluster_low bytes reflect start_cluster

- assert true
- var dev = MockDirentDev new
- dev = dev with sector
- dev = dev with sector
- buf push
- buf push
- buf push
- assert true
   - Expected: h1.start_cluster equals `2u32`
   - Expected: cl_low equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root_dir = _make_root_dir_with_test_txt()
val fs = _make_fs_with_rootdir(root_dir)
val h_result = fs.open("/TEST.TXT")
assert_true(h_result.is_ok())
val h0 = h_result.unwrap()
# FAT at LBA 32: all free.  Root-dir at LBA 64.  Data at LBA 64+(N-2).
var dev = MockDirentDev.new()
dev = dev.with_sector(_fat_lba(), _zero_sector())
dev = dev.with_sector(_root_dir_lba(), root_dir)
var buf: [u8] = []
buf.push(0xAAu8)
buf.push(0xBBu8)
buf.push(0xCCu8)
val w_result = fs.write(dev, h0, buf)
assert_true(w_result.is_ok())
val h1 = w_result.unwrap()
# allocate_cluster always picks cluster 2 from a fresh FAT.
expect(h1.start_cluster).to_equal(2u32)
# Re-read root-dir sector from device; entry at dirent_offset=32,
# so first_cluster_low is at sector byte 32+26=58.
val dirent_sec = dev.get_sector(_root_dir_lba())
val cl_low = _peek16_dirent(dirent_sec, 58)
expect(cl_low).to_equal(2u32)
```

</details>

#### after write, dirent first_cluster_high bytes are zero for cluster < 65536

- assert true
- var dev = MockDirentDev new
- dev = dev with sector
- dev = dev with sector
- buf push
- assert true
   - Expected: cl_high equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root_dir = _make_root_dir_with_test_txt()
val fs = _make_fs_with_rootdir(root_dir)
val h_result = fs.open("/TEST.TXT")
assert_true(h_result.is_ok())
val h0 = h_result.unwrap()
var dev = MockDirentDev.new()
dev = dev.with_sector(_fat_lba(), _zero_sector())
dev = dev.with_sector(_root_dir_lba(), root_dir)
var buf: [u8] = []
buf.push(0x01u8)
val w_result = fs.write(dev, h0, buf)
assert_true(w_result.is_ok())
# entry at dirent_offset=32, cluster_high at 32+20=52
val dirent_sec = dev.get_sector(_root_dir_lba())
val cl_high = _peek16_dirent(dirent_sec, 52)
expect(cl_high).to_equal(0u32)
```

</details>

#### after write, dirent file_size bytes equal bytes written

- assert true
- var dev = MockDirentDev new
- dev = dev with sector
- dev = dev with sector
- buf push
- buf push
- buf push
- buf push
- assert true
   - Expected: fsz equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root_dir = _make_root_dir_with_test_txt()
val fs = _make_fs_with_rootdir(root_dir)
val h_result = fs.open("/TEST.TXT")
assert_true(h_result.is_ok())
val h0 = h_result.unwrap()
var dev = MockDirentDev.new()
dev = dev.with_sector(_fat_lba(), _zero_sector())
dev = dev.with_sector(_root_dir_lba(), root_dir)
var buf: [u8] = []
buf.push(0x11u8)
buf.push(0x22u8)
buf.push(0x33u8)
buf.push(0x44u8)
val w_result = fs.write(dev, h0, buf)
assert_true(w_result.is_ok())
# entry at dirent_offset=32, file_size at 32+28=60
val dirent_sec = dev.get_sector(_root_dir_lba())
val fsz = _peek32_dirent(dirent_sec, 60)
expect(fsz).to_equal(4u32)
```

</details>

### root_dir_data cache coherence after write

#### root_dir_data cache file_size matches on-disk dirent after write

- assert true
- var dev = MockDirentDev new
- dev = dev with sector
- dev = dev with sector
- buf push
- buf push
- assert true
- assert true
   - Expected: st.size equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root_dir = _make_root_dir_with_test_txt()
val fs = _make_fs_with_rootdir(root_dir)
val h_result = fs.open("/TEST.TXT")
assert_true(h_result.is_ok())
val h0 = h_result.unwrap()
var dev = MockDirentDev.new()
dev = dev.with_sector(_fat_lba(), _zero_sector())
dev = dev.with_sector(_root_dir_lba(), root_dir)
var buf: [u8] = []
buf.push(0xFFu8)
buf.push(0xFEu8)
val w_result = fs.write(dev, h0, buf)
assert_true(w_result.is_ok())
# stat() reads from root_dir_data cache — should see updated size.
val st_result = fs.stat("/TEST.TXT")
assert_true(st_result.is_ok())
val st = st_result.unwrap()
expect(st.size).to_equal(2u64)
```

</details>

### dirent_sector=0 handle skips _update_dirent

#### write with dirent_sector=0 succeeds without updating any sector

- var dev = MockDirentDev new
- dev = dev with sector
- buf push
- assert true
   - Expected: h1.file_size equals `1u64`
   - Expected: h1.dirent_sector equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fs = Fat32Filesystem.make_for_alloc_test(32u32, 64u32, 512u32, 1u32, 8u32)
val h0 = _make_bare_handle()
var dev = MockDirentDev.new()
dev = dev.with_sector(_fat_lba(), _zero_sector())
var buf: [u8] = []
buf.push(0xDDu8)
val w_result = fs.write(dev, h0, buf)
assert_true(w_result.is_ok())
val h1 = w_result.unwrap()
expect(h1.file_size).to_equal(1u64)
# No root-dir sector was registered; device would return zeroed sector
# for any LBA, so no crash from _update_dirent — it skips entirely.
expect(h1.dirent_sector).to_equal(0u64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
