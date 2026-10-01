# Disk Image Builder Specification

> Tests covering disk_image.build -- FAT32 builder defect fixes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Disk Image Builder Specification

## Scenarios

### disk_image.build -- FAT32 builder defect fixes

#### accepts every selected SimpleOS font alias as a nested FAT path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts every selected SimpleOS font alias as a nested FAT path
   - Expected: rt_dir_create_all(root) is true
   - Expected: result.is_ok() is true
   - Expected: _od_hex(out_path, root_dir_offset, 12) equals `53 59 53 20 20 20 20 20 20 20 20 10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts every selected SimpleOS font alias as a nested FAT path")
val root = "/tmp/disk_image_builder_spec_font_aliases"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)
var fonts: [PayloadEntry] = []
var byte: u8 = 1u8
for candidate in selected_font_asset_candidates():
    fonts.push(PayloadEntry(
        path: simpleos_font_asset_short_name(candidate),
        data: [byte],
        guest_path: simpleos_font_asset_guest_path(candidate)
    ))
    byte = byte + 1u8
val out_path = root + "/disk.img"
val result = build(DiskImageConfig(
    size_mb: 1u64,
    payloads: [],
    nested_payloads: fonts
), out_path)
expect(result.is_ok()).to_equal(true)
val root_dir_offset: i64 = 34 * 512
expect(_od_hex(out_path, root_dir_offset, 12)).to_equal("53 59 53 20 20 20 20 20 20 20 20 10")
_cleanup(root)
```

</details>

#### builds when nested_payloads is omitted from DiskImageConfig

- builds when nested_payloads is omitted from DiskImageConfig
   - Expected: rt_dir_create_all(root) is true
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds when nested_payloads is omitted from DiskImageConfig")
"""Bug #1: omitting `nested_payloads` used to bind it to `nil` at
runtime (a struct-literal-init gap) and crash `for p in cfg.payloads:`
even though `payloads` was set correctly. `nested_payloads` now
defaults to `[]` so flat-root-only callers don't need to pass it."""
val root = "/tmp/disk_image_builder_spec_defaults"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)
val out_path = root + "/disk.img"
val cfg = DiskImageConfig(size_mb: 1u64, payloads: [PayloadEntry(path: "A.TXT", data: [1u8, 2u8, 3u8], guest_path: "")])
val result = build(cfg, out_path)
expect(result.is_ok()).to_equal(true)
_cleanup(root)
```

</details>

#### stores flat-root dirent names as proper 8.3 (dot dropped, uppercased)

- stores flat-root dirent names as proper 8.3 (dot dropped, uppercased)
   - Expected: rt_dir_create_all(root) is true
   - Expected: result.is_ok() is true
   - Expected: _od_hex(out_path, root_dir_offset, 11) equals `46 53 45 58 45 43 42 47 45 4c 46`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores flat-root dirent names as proper 8.3 (dot dropped, uppercased)")
"""Bug #3: build() previously passed p.path verbatim to
_build_dir_entry, so "FSEXECBG.ELF" was stored as the 11 raw bytes
"FSEXECBG.EL" (dot kept, truncated) instead of the 8.3 form
"FSEXECBGELF" the C reader's fat32_find_file expects."""
val root = "/tmp/disk_image_builder_spec_83name"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)
val out_path = root + "/disk.img"
val cfg = DiskImageConfig(size_mb: 1u64, payloads: [PayloadEntry(path: "FSEXECBG.ELF", data: [9u8, 9u8], guest_path: "")])
val result = build(cfg, out_path)
expect(result.is_ok()).to_equal(true)

# Single flat payload -> fat_sectors is small (1 sector: 3 reserved +
# 1 data cluster = 4 entries * 4 bytes = 16 bytes, well under 512).
# Root dir cluster therefore starts at sector 32 + 2*1 = 34.
val root_dir_offset: i64 = 34 * 512
expect(_od_hex(out_path, root_dir_offset, 11)).to_equal("46 53 45 58 45 43 42 47 45 4c 46")
_cleanup(root)
```

</details>

#### writes standard VFAT slots before nested directory and leaf aliases

- writes standard VFAT slots before nested directory and leaf aliases
   - Expected: rt_dir_create_all(root) is true
   - Expected: result.is_ok() is true
   - Expected: _od_hex(out_path, root_dir_offset, 14) equals `41 4c 00 6f 00 6e 00 67 00 44 00 0f 00 1f`
   - Expected: _od_hex(out_path, root_dir_offset + 28, 4) equals `72 00 79 00`
   - Expected: _od_hex(out_path, root_dir_offset + 32, 12) equals `4c 4f 4e 47 44 49 7e 31 20 20 20 10`
   - Expected: _od_hex(out_path, long_dir_offset, 14) equals `42 74 00 74 00 66 00 00 00 ff ff 0f 00 44`
   - Expected: _od_hex(out_path, long_dir_offset + 32, 14) equals `01 4c 00 6f 00 6e 00 67 00 46 00 0f 00 44`
   - Expected: _od_hex(out_path, long_dir_offset + 64, 11) equals `4c 4f 4e 47 46 49 7e 31 54 54 46`
   - Expected: _od_hex(out_path, long_dir_offset + 64 + 26, 6) equals `03 00 01 00 00 00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes standard VFAT slots before nested directory and leaf aliases")
val root = "/tmp/disk_image_builder_spec_lfn_bytes"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)
val out_path = root + "/disk.img"
val result = build(DiskImageConfig(
    size_mb: 1u64,
    payloads: [],
    nested_payloads: [PayloadEntry(
        path: "LONGFI~1.TTF",
        data: [0xAAu8],
        guest_path: "/LongDirectory/LongFileName.ttf"
    )]
), out_path)
expect(result.is_ok()).to_equal(true)

# One data cluster and one directory cluster keep fat_size_32 at one:
# root is sector 34, payload cluster 3 is sector 35, directory cluster
# 4 is sector 36. "LongDirectory" is exactly 13 UTF-16 code units.
val root_dir_offset: i64 = 34 * 512
expect(_od_hex(out_path, root_dir_offset, 14)).to_equal("41 4c 00 6f 00 6e 00 67 00 44 00 0f 00 1f")
expect(_od_hex(out_path, root_dir_offset + 28, 4)).to_equal("72 00 79 00")
expect(_od_hex(out_path, root_dir_offset + 32, 12)).to_equal("4c 4f 4e 47 44 49 7e 31 20 20 20 10")

# The 16-character leaf needs slots 2 then 1. Slot 2 contains "ttf",
# one NUL, and 0xFFFF fill; both slots use the alias checksum 0x44.
val long_dir_offset: i64 = 36 * 512
expect(_od_hex(out_path, long_dir_offset, 14)).to_equal("42 74 00 74 00 66 00 00 00 ff ff 0f 00 44")
expect(_od_hex(out_path, long_dir_offset + 32, 14)).to_equal("01 4c 00 6f 00 6e 00 67 00 46 00 0f 00 44")
expect(_od_hex(out_path, long_dir_offset + 64, 11)).to_equal("4c 4f 4e 47 46 49 7e 31 54 54 46")
expect(_od_hex(out_path, long_dir_offset + 64 + 26, 6)).to_equal("03 00 01 00 00 00")
_cleanup(root)
```

</details>

#### encodes BMP and astral UTF-8 leaf names as UTF-16LE LFN units

- encodes BMP and astral UTF-8 leaf names as UTF-16LE LFN units
   - Expected: rt_dir_create_all(root) is true
   - Expected: result.is_ok() is true
   - Expected: _od_hex(out_path, root_dir_offset + 1, 10) equals `e5 65 2c 67 3d d8 00 de 2e 00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes BMP and astral UTF-8 leaf names as UTF-16LE LFN units")
val root = "/tmp/disk_image_builder_spec_lfn_unicode"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)
val out_path = root + "/disk.img"
val result = build(DiskImageConfig(
    size_mb: 1u64,
    payloads: [],
    nested_payloads: [PayloadEntry(path: "UNICOD~1.TTF", data: [0xAAu8], guest_path: "/日本😀.ttf")]
), out_path)
expect(result.is_ok()).to_equal(true)
val root_dir_offset: i64 = 34 * 512
# 日 (U+65E5), 本 (U+672C), 😀 (U+D83D U+DE00), and '.' in UTF-16LE.
expect(_od_hex(out_path, root_dir_offset + 1, 10)).to_equal("e5 65 2c 67 3d d8 00 de 2e 00")
_cleanup(root)
```

</details>

#### permits an astral surrogate pair to cross a 13-unit LFN slot boundary

- permits an astral surrogate pair to cross a 13-unit LFN slot boundary
   - Expected: rt_dir_create_all(root) is true
   - Expected: result.is_ok() is true
   - Expected: _od_hex(out_path, root_dir_offset, 3) equals `42 00 de`
   - Expected: _od_hex(out_path, root_dir_offset + 32, 1) equals `01`
   - Expected: _od_hex(out_path, root_dir_offset + 62, 2) equals `3d d8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("permits an astral surrogate pair to cross a 13-unit LFN slot boundary")
val root = "/tmp/disk_image_builder_spec_lfn_surrogate_boundary"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)
val out_path = root + "/disk.img"
val result = build(DiskImageConfig(
    size_mb: 1u64,
    payloads: [],
    nested_payloads: [PayloadEntry(path: "BOUNDA~1.TTF", data: [0xAAu8], guest_path: "/abcdefghijkl😀.ttf")]
), out_path)
expect(result.is_ok()).to_equal(true)
val root_dir_offset: i64 = 34 * 512
# Ordinal 1 ends with the high surrogate; ordinal 2 begins with low.
expect(_od_hex(out_path, root_dir_offset, 3)).to_equal("42 00 de")
expect(_od_hex(out_path, root_dir_offset + 32, 1)).to_equal("01")
expect(_od_hex(out_path, root_dir_offset + 62, 2)).to_equal("3d d8")
_cleanup(root)
```

</details>

#### assigns unique short aliases to colliding 14-character directory names

- assigns unique short aliases to colliding 14-character directory names
   - Expected: rt_dir_create_all(root) is true
   - Expected: result.is_ok() is true
   - Expected: _od_hex(out_path, root_dir_offset, 14) equals `42 41 00 00 00 ff ff ff ff ff ff 0f 00 1f`
   - Expected: _od_hex(out_path, root_dir_offset + 64, 11) equals `4c 4f 4e 47 44 49 7e 31 20 20 20`
   - Expected: _od_hex(out_path, root_dir_offset + 96, 14) equals `42 42 00 00 00 ff ff ff ff ff ff 0f 00 40`
   - Expected: _od_hex(out_path, root_dir_offset + 160, 11) equals `4c 4f 4e 47 44 49 7e 32 20 20 20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns unique short aliases to colliding 14-character directory names")
val root = "/tmp/disk_image_builder_spec_lfn_collision"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)
val out_path = root + "/disk.img"
val result = build(DiskImageConfig(
    size_mb: 1u64,
    payloads: [],
    nested_payloads: [
        PayloadEntry(path: "A", data: [1u8], guest_path: "/LongDirectoryA/A"),
        PayloadEntry(path: "B", data: [2u8], guest_path: "/LongDirectoryB/B")
    ]
), out_path)
expect(result.is_ok()).to_equal(true)
val root_dir_offset: i64 = 34 * 512
expect(_od_hex(out_path, root_dir_offset, 14)).to_equal("42 41 00 00 00 ff ff ff ff ff ff 0f 00 1f")
expect(_od_hex(out_path, root_dir_offset + 64, 11)).to_equal("4c 4f 4e 47 44 49 7e 31 20 20 20")
expect(_od_hex(out_path, root_dir_offset + 96, 14)).to_equal("42 42 00 00 00 ff ff ff ff ff ff 0f 00 40")
expect(_od_hex(out_path, root_dir_offset + 160, 11)).to_equal("4c 4f 4e 47 44 49 7e 32 20 20 20")
_cleanup(root)
```

</details>

#### chains a directory that needs more than one 512-byte cluster

- chains a directory that needs more than one 512-byte cluster
   - Expected: rt_dir_create_all(root) is true
   - Expected: result.is_ok() is true
   - Expected: _od_hex(out_path, ofl_fat_entry_offset, 12) equals `17 00 00 00 18 00 00 00 ff ff ff 0f`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains a directory that needs more than one 512-byte cluster")
val root = "/tmp/disk_image_builder_spec_lfn_dir_chain"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)
var fonts: [PayloadEntry] = []
for candidate in selected_font_asset_candidates():
    fonts.push(PayloadEntry(path: "FONT", data: [1u8], guest_path: "/" + candidate.local_path))
val out_path = root + "/disk.img"
val result = build(DiskImageConfig(size_mb: 1u64, payloads: [], nested_payloads: fonts), out_path)
expect(result.is_ok()).to_equal(true)
# Sixteen file clusters are 3..18; assets/fonts/google-fonts occupy
# 19..21; /ofl starts at cluster 22 and needs three clusters.
val ofl_fat_entry_offset: i64 = 32 * 512 + 22 * 4
expect(_od_hex(out_path, ofl_fat_entry_offset, 12)).to_equal("17 00 00 00 18 00 00 00 ff ff ff 0f")
_cleanup(root)
```

</details>

#### rejects LFN root entries that exceed the fixed root cluster

- rejects LFN root entries that exceed the fixed root cluster
   - Expected: rt_dir_create_all(root) is true
   - Expected: result.is_ok() is false
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects LFN root entries that exceed the fixed root cluster")
val root = "/tmp/disk_image_builder_spec_lfn_root_capacity"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)
var nested: [PayloadEntry] = []
var i: i64 = 0
while i < 6:
    nested.push(PayloadEntry(path: "A", data: [1u8], guest_path: "/LongDirectory" + i.to_text() + "/A"))
    i = i + 1
val result = build(DiskImageConfig(size_mb: 1u64, payloads: [], nested_payloads: nested), root + "/disk.img")
expect(result.is_ok()).to_equal(false)
match result:
    Ok(_):
        expect(false).to_equal(true)
    Err(e):
        expect(e).to_contain("fixed root cluster holds 16")
_cleanup(root)
```

</details>

#### sizes the FAT from the payload cluster count instead of a fixed 128 sectors

- sizes the FAT from the payload cluster count instead of a fixed 128 sectors
   - Expected: rt_dir_create_all(root) is true
   - Expected: result.is_ok() is true
   - Expected: _od_hex(out_path, 36, 4) equals `02 00 00 00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sizes the FAT from the payload cluster count instead of a fixed 128 sectors")
"""Bug #4: FAT was fixed at 128 sectors (16,384 entries, ~8.39 MB at
512 B/cluster); a larger payload's cluster chain silently overran
FAT1 into FAT2 and then into the root directory. fat_size_32 in the
BPB (offset 36, LE u32) must now reflect the actual sectors needed
instead of always being 128 (0x80): a 64,100-byte payload needs
ceil(64100/512)=126 data clusters -> 129 FAT entries (3 reserved +
126) -> ceil(129*4/512)=2 sectors. This is also proven at production
scale end-to-end: a real 8,400,000-byte ELF payload (fat_size_32=129,
0x81) built by this same `build()` was booted under QEMU and its C
reader (fat32_find_file) found and ran it -- see
doc/08_tracking/bug/disk_image_fat32_builder_defects.md #4."""
val root = "/tmp/disk_image_builder_spec_fatsize"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)
val out_path = root + "/disk.img"
val payload = _repeat_byte(64100, 1u8)
val cfg = DiskImageConfig(size_mb: 1u64, payloads: [PayloadEntry(path: "BIG.BIN", data: payload, guest_path: "")])
val result = build(cfg, out_path)
expect(result.is_ok()).to_equal(true)
expect(_od_hex(out_path, 36, 4)).to_equal("02 00 00 00")
_cleanup(root)
```

</details>

#### errors clearly instead of silently overflowing when a payload cannot fit

- errors clearly instead of silently overflowing when a payload cannot fit
   - Expected: rt_dir_create_all(root) is true
   - Expected: result.is_ok() is false
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("errors clearly instead of silently overflowing when a payload cannot fit")
"""Bug #4 (error path): a payload whose data + FAT + reserved sectors
exceed the requested image size must return a clear Err, not silently
truncate structural regions into each other. A 1.1 MB payload cannot
fit a 1 MiB (2048-sector) image once FAT + reserved + root overhead
is included."""
val root = "/tmp/disk_image_builder_spec_toobig"
_cleanup(root)
expect(rt_dir_create_all(root)).to_equal(true)
val out_path = root + "/disk.img"
val payload = _repeat_byte(1100000, 1u8)
val cfg = DiskImageConfig(size_mb: 1u64, payloads: [PayloadEntry(path: "BIG.BIN", data: payload, guest_path: "")])
val result = build(cfg, out_path)
expect(result.is_ok()).to_equal(false)
match result:
    Ok(_):
        expect(false).to_equal(true)
    Err(e):
        expect(e).to_contain("increase size_mb")
_cleanup(root)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/disk_image_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering disk_image.build -- FAT32 builder defect fixes.
- disk_image.build -- FAT32 builder defect fixes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `809f24b53b5239dc42c14b3480ab76a3a6cf009bedcbc638a5a6fd3468610dc7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `809f24b53b5239dc42c14b3480ab76a3a6cf009bedcbc638a5a6fd3468610dc7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `809f24b53b5239dc42c14b3480ab76a3a6cf009bedcbc638a5a6fd3468610dc7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/port/disk_image_builder_spec.spl
mirror: doc/06_spec/01_unit/os/port/disk_image_builder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/port/disk_image_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/disk_image_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/disk_image_builder_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts every selected SimpleOS font alias as a nested FAT path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/disk_image_builder_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds when nested_payloads is omitted from DiskImageConfig' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/disk_image_builder_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores flat-root dirent names as proper 8.3 (dot dropped, uppercased)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
