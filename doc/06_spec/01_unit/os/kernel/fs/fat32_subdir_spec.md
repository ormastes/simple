# FAT32 Subdirectory Traversal — Wave-4f Spec

> Before this wave the driver could only see the root directory, so an in-guest

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FAT32 Subdirectory Traversal — Wave-4f Spec

Before this wave the driver could only see the root directory, so an in-guest

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/fs/fat32_subdir_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Lane:** B2 of `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`
Before this wave the driver could only see the root directory, so an in-guest
source tree (an LLVM checkout is ~150k files in nested directories) could not
exist at all. These scenarios drive `resolve_path` / `open_at` / `stat_at`
against a synthetic in-memory FAT32 volume and prove that each path component
is really walked — not merely that the last component happens to be findable.

Synthetic volume geometry (fat_start=32, data_start=64, bps=512, spc=1,
cluster_size=512, data_clusters=8, root_cluster=2):

    cluster 2  (LBA 64)  root : dir A -> cluster 3
                                FILE.O  -> cluster 9, size 11   (decoy)
    cluster 3  (LBA 65)  /A   : "." -> 3, ".." -> 0 (root), dir B -> cluster 4
    cluster 4  (LBA 66)  /A/B : "." -> 4, ".." -> 3, dir C -> cluster 5
    cluster 5  (LBA 67)  /A/B/C : "." -> 5, ".." -> 4,
                                FILE.O -> cluster 6, size 77
                                "LongName.txt" (LFN) -> cluster 7, size 5

The two `FILE.O` entries share a basename but carry **different sizes**, so a
resolver that silently ignores intermediate components cannot pass.

## Scenarios

### fat32 subdirectory traversal — wave-4f

### path splitting

#### drops empty components and yields one entry per name

- drops empty components and yields one entry per name
- split a three-deep absolute path
   - Expected: parts.len() equals `4`
   - Expected: parts[0] equals `A`
   - Expected: parts[3] equals `FILE.O`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("drops empty components and yields one entry per name")
step("split a three-deep absolute path")
val parts = fat32_split_path("/A/B/C/FILE.O")
expect(parts.len()).to_equal(4)
expect(parts[0]).to_equal("A")
expect(parts[3]).to_equal("FILE.O")
```

</details>

#### treats the root path as having no components

- treats the root path as having no components
- split "/"
   - Expected: fat32_split_path("/").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("treats the root path as having no components")
step("split \"/\"")
expect(fat32_split_path("/").len()).to_equal(0)
```

</details>

### nested read path

#### resolves /A/B/C/FILE.O to the nested file, not the root decoy

- resolves /A/B/C/FILE.O to the nested file, not the root decoy
- stat the root FILE.O — the decoy, size 11
   - Expected: root_st.unwrap().size equals `11u64`
- stat the three-deep FILE.O — the real one, size 77
   - Expected: nested_st.unwrap().size equals `77u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("resolves /A/B/C/FILE.O to the nested file, not the root decoy")
val fs = _make_fs()
val dev = _make_dev()
step("stat the root FILE.O — the decoy, size 11")
val root_st = fs.stat_at(dev, "/FILE.O")
assert_true(root_st.is_ok())
expect(root_st.unwrap().size).to_equal(11u64)
step("stat the three-deep FILE.O — the real one, size 77")
val nested_st = fs.stat_at(dev, "/A/B/C/FILE.O")
assert_true(nested_st.is_ok())
expect(nested_st.unwrap().size).to_equal(77u64)
```

</details>

#### open_at on the nested file yields its own first cluster and size

- open_at on the nested file yields its own first cluster and size
- open /A/B/C/FILE.O
   - Expected: h.start_cluster equals `6u32`
   - Expected: h.file_size equals `77u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("open_at on the nested file yields its own first cluster and size")
val fs = _make_fs()
val dev = _make_dev()
step("open /A/B/C/FILE.O")
val h_result = fs.open_at(dev, "/A/B/C/FILE.O")
assert_true(h_result.is_ok())
val h = h_result.unwrap()
expect(h.start_cluster).to_equal(6u32)
expect(h.file_size).to_equal(77u64)
```

</details>

#### records the dirent address inside the containing subdirectory

- records the dirent address inside the containing subdirectory
- resolve /A/B/C/FILE.O and read back its on-disk dirent address
   - Expected: loc.dir_cluster equals `5u32`
   - Expected: loc.dirent_sector equals `67u64)   # cluster 5 -> LBA 64+(5-2`
   - Expected: loc.dirent_offset equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("records the dirent address inside the containing subdirectory")
val fs = _make_fs()
val dev = _make_dev()
step("resolve /A/B/C/FILE.O and read back its on-disk dirent address")
val loc_result = fs.resolve_path(dev, "/A/B/C/FILE.O")
assert_true(loc_result.is_ok())
val loc = loc_result.unwrap()
assert_true(loc.found)
expect(loc.dir_cluster).to_equal(5u32)
expect(loc.dirent_sector).to_equal(67u64)   # cluster 5 -> LBA 64+(5-2)
expect(loc.dirent_offset).to_equal(64)
```

</details>

#### reports intermediate components as directories

- reports intermediate components as directories
- stat /A/B


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports intermediate components as directories")
val fs = _make_fs()
val dev = _make_dev()
step("stat /A/B")
val st = fs.stat_at(dev, "/A/B")
assert_true(st.is_ok())
assert_true(st.unwrap().is_dir)
```

</details>

#### descends through a directory carrying extra attribute bits

- descends through a directory carrying extra attribute bits
- /A/B/D has attr 0x30 (DIRECTORY|ARCHIVE) and shares C's cluster
   - Expected: st.unwrap().size equals `77u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("descends through a directory carrying extra attribute bits")
val fs = _make_fs()
val dev = _make_dev()
step("/A/B/D has attr 0x30 (DIRECTORY|ARCHIVE) and shares C's cluster")
val st = fs.stat_at(dev, "/A/B/D/FILE.O")
assert_true(st.is_ok())
expect(st.unwrap().size).to_equal(77u64)
```

</details>

#### refuses to open a directory as a file

- refuses to open a directory as a file
- open_at /A/B must fail
   - Expected: h.unwrap_err() equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("refuses to open a directory as a file")
val fs = _make_fs()
val dev = _make_dev()
step("open_at /A/B must fail")
val h = fs.open_at(dev, "/A/B")
assert_true(h.is_err())
expect(h.unwrap_err()).to_equal(-2)
```

</details>

### long filenames inside a subdirectory

#### matches an LFN entry three levels down

- matches an LFN entry three levels down
- stat /A/B/C/LongName.txt by its long name
   - Expected: st.unwrap().size equals `5u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("matches an LFN entry three levels down")
val fs = _make_fs()
val dev = _make_dev()
step("stat /A/B/C/LongName.txt by its long name")
val st = fs.stat_at(dev, "/A/B/C/LongName.txt")
assert_true(st.is_ok())
expect(st.unwrap().size).to_equal(5u64)
```

</details>

#### still matches the same entry by its 8.3 short name

- still matches the same entry by its 8.3 short name
- stat /A/B/C/LONGNA~1.TXT
   - Expected: st.unwrap().size equals `5u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("still matches the same entry by its 8.3 short name")
val fs = _make_fs()
val dev = _make_dev()
step("stat /A/B/C/LONGNA~1.TXT")
val st = fs.stat_at(dev, "/A/B/C/LONGNA~1.TXT")
assert_true(st.is_ok())
expect(st.unwrap().size).to_equal(5u64)
```

</details>

### dot and dot-dot components

#### treats \

- treats \
- resolve /A/B/./C/FILE.O
   - Expected: st.unwrap().size equals `77u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("treats \")
val fs = _make_fs()
val dev = _make_dev()
step("resolve /A/B/./C/FILE.O")
val st = fs.stat_at(dev, "/A/B/./C/FILE.O")
assert_true(st.is_ok())
expect(st.unwrap().size).to_equal(77u64)
```

</details>

#### walks \

- walks \
- resolve /A/B/C/../C/FILE.O — down to C, up to B, back into C
   - Expected: st.unwrap().size equals `77u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("walks \")
val fs = _make_fs()
val dev = _make_dev()
step("resolve /A/B/C/../C/FILE.O — down to C, up to B, back into C")
val st = fs.stat_at(dev, "/A/B/C/../C/FILE.O")
assert_true(st.is_ok())
expect(st.unwrap().size).to_equal(77u64)
```

</details>

#### maps a \

- maps a \
- climb all the way out and land on the root decoy, size 11
   - Expected: st.unwrap().size equals `11u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps a \")
val fs = _make_fs()
val dev = _make_dev()
step("climb all the way out and land on the root decoy, size 11")
val st = fs.stat_at(dev, "/A/B/C/../../../FILE.O")
assert_true(st.is_ok())
expect(st.unwrap().size).to_equal(11u64)
```

</details>

### fail-closed behaviour

#### returns ENOENT when an intermediate directory does not exist

- returns ENOENT when an intermediate directory does not exist
- resolve /A/NOPE/FILE.O
   - Expected: r.unwrap_err() equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns ENOENT when an intermediate directory does not exist")
val fs = _make_fs()
val dev = _make_dev()
step("resolve /A/NOPE/FILE.O")
val r = fs.resolve_path(dev, "/A/NOPE/FILE.O")
assert_true(r.is_err())
expect(r.unwrap_err()).to_equal(-2)
```

</details>

#### returns ENOENT for a name that only exists deeper in the tree

- returns ENOENT for a name that only exists deeper in the tree
- FILE.O lives in /A/B/C, not in /A
   - Expected: r.unwrap_err() equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns ENOENT for a name that only exists deeper in the tree")
val fs = _make_fs()
val dev = _make_dev()
step("FILE.O lives in /A/B/C, not in /A")
val r = fs.resolve_path(dev, "/A/FILE.O")
assert_true(r.is_err())
expect(r.unwrap_err()).to_equal(-2)
```

</details>

#### refuses to descend through a regular file

- refuses to descend through a regular file
- resolve /FILE.O/X — FILE.O is not a directory
   - Expected: r.unwrap_err() equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("refuses to descend through a regular file")
val fs = _make_fs()
val dev = _make_dev()
step("resolve /FILE.O/X — FILE.O is not a directory")
val r = fs.resolve_path(dev, "/FILE.O/X")
assert_true(r.is_err())
expect(r.unwrap_err()).to_equal(-2)
```

</details>

#### rejects a path with no components

- rejects a path with no components
- resolve "/"
   - Expected: r.unwrap_err() equals `-22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a path with no components")
val fs = _make_fs()
val dev = _make_dev()
step("resolve \"/\"")
val r = fs.resolve_path(dev, "/")
assert_true(r.is_err())
expect(r.unwrap_err()).to_equal(-22)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b619e243b8e0bfd7604e181956a517e921c4fc6588cc2574b561cf02b4346865`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b619e243b8e0bfd7604e181956a517e921c4fc6588cc2574b561cf02b4346865`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b619e243b8e0bfd7604e181956a517e921c4fc6588cc2574b561cf02b4346865`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/fs/fat32_subdir_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/fs/fat32_subdir_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/fs/fat32_subdir_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/fs/fat32_subdir_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/fs/fat32_subdir_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/fs/fat32_subdir_spec.spl:221:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drops empty components and yields one entry per name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/fat32_subdir_spec.spl:230:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats the root path as having no components' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/fat32_subdir_spec.spl:238:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves /A/B/C/FILE.O to the nested file, not the root decoy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
