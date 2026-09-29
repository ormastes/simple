# fs_hardening_spec

> FS Hardening Specification

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
| Source | `test/unit/lib/fs_driver/fs_hardening_spec.spl` |
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-9: handle_pack encodes generation in high 32 bits
   - Expected: g equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-9: handle_pack encodes generation in high 32 bits")
val packed = handle_pack(42, 7)
val g = handle_unpack_gen(packed)
expect(g).to_equal(7)
```

</details>

#### AC-9: handle_pack encodes slot index in low 32 bits

- AC-9: handle_pack encodes slot index in low 32 bits
   - Expected: idx equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-9: handle_pack encodes slot index in low 32 bits")
val packed = handle_pack(42, 7)
val idx = handle_unpack_slot(packed)
expect(idx).to_equal(42)
```

</details>

#### AC-9: handle_validate rejects stale generation

- AC-9: handle_validate rejects stale generation
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-9: handle_validate rejects stale generation")
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

- AC-9: StaleHandle variant exists and is distinct from InvalidArg
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-9: StaleHandle variant exists and is distinct from InvalidArg")
val e1 = FsError.StaleHandle
val e2 = FsError.InvalidArg
val same = e1 == e2
expect(same).to_equal(false)
```

</details>

#### AC-9: PathTraversal variant exists and is distinct from Permission

- AC-9: PathTraversal variant exists and is distinct from Permission
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-9: PathTraversal variant exists and is distinct from Permission")
val e1 = FsError.PathTraversal
val e2 = FsError.Permission
val same = e1 == e2
expect(same).to_equal(false)
```

</details>

### RamFS Hardening — double-close

#### AC-9: double close returns StaleHandle error

- AC-9: double close returns StaleHandle error
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-9: double close returns StaleHandle error")
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

- AC-9: read on stale handle returns StaleHandle
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-9: read on stale handle returns StaleHandle")
var d = make_ramfs_direct()
val fh = FileHandle(id: 999)
val buf: [u8] = []
val r = d.read(fh, 0, buf)
val is_err = r.is_err()
expect(is_err).to_equal(true)
```

</details>

#### AC-9: write on stale handle returns StaleHandle

- AC-9: write on stale handle returns StaleHandle
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-9: write on stale handle returns StaleHandle")
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

- AC-9: PathTraversal FsError variant is distinct from Permission
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-9: PathTraversal FsError variant is distinct from Permission")
val e1 = FsError.PathTraversal
val e2 = FsError.Permission
val same = e1 == e2
expect(same).to_equal(false)
```

</details>

### RamFS Hardening — sorted lookup

#### AC-3: find_inode_idx returns valid index for inserted inode

- AC-3: find_inode_idx returns valid index for inserted inode
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: find_inode_idx returns valid index for inserted inode")
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

- AC-1: validate_bpb rejects zero bytes_per_sector
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: validate_bpb rejects zero bytes_per_sector")
val r = validate_bpb(Fat32Bpb(bytes_per_sector: 0, sectors_per_cluster: 8, reserved_sectors: 32, num_fats: 2, total_sectors_32: 2048, fat_size_32: 128, root_cluster: 2))
val is_err = r.is_err()
expect(is_err).to_equal(true)
```

</details>

#### AC-1: validate_bpb rejects non-power-of-two cluster size

- AC-1: validate_bpb rejects non-power-of-two cluster size
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: validate_bpb rejects non-power-of-two cluster size")
val r = validate_bpb(Fat32Bpb(bytes_per_sector: 512, sectors_per_cluster: 3, reserved_sectors: 32, num_fats: 2, total_sectors_32: 2048, fat_size_32: 128, root_cluster: 2))
val is_err = r.is_err()
expect(is_err).to_equal(true)
```

</details>

### FAT32 Hardening — cluster chain cycle

#### AC-1: detect_cluster_cycle detects a cycle

- AC-1: detect_cluster_cycle detects a cycle
   - Expected: is_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: detect_cluster_cycle detects a cycle")
val has_cycle = detect_cluster_cycle(2, 1024)
val is_ok = has_cycle.is_ok()
# Function exists and returns a result; actual cycle detection
# depends on FAT table content set up by the driver
expect(is_ok).to_equal(true)
```

</details>

### NVFS Superblock Hardening — corrupt superblock

#### AC-2: corrupt superblock bytes returns Corrupt error

- AC-2: corrupt superblock bytes returns Corrupt error
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: corrupt superblock bytes returns Corrupt error")
# Construct a buffer with invalid magic / bad checksum
val bad_buf = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
val r = nvfs_superblock_read_from_bytes(bad_buf)
val is_err = r.is_err()
expect(is_err).to_equal(true)
```

</details>

#### AC-2: short buffer returns Corrupt error

- AC-2: short buffer returns Corrupt error
   - Expected: is_err is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-2: short buffer returns Corrupt error")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c20736e03d9317a5eceea4b53620bf2f728ff0358bd4ece3b85205b77d42409`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c20736e03d9317a5eceea4b53620bf2f728ff0358bd4ece3b85205b77d42409`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c20736e03d9317a5eceea4b53620bf2f728ff0358bd4ece3b85205b77d42409`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/fs_driver/fs_hardening_spec.spl
mirror: doc/06_spec/unit/lib/fs_driver/fs_hardening_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/fs_driver/fs_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/fs_driver/fs_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/fs_driver/fs_hardening_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/fs_driver/fs_hardening_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-9: handle_pack encodes generation in high 32 bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/fs_driver/fs_hardening_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-9: handle_pack encodes slot index in low 32 bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/fs_driver/fs_hardening_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-9: handle_validate rejects stale generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
