# mount_table_nvfs_posix_dispatch_spec

> MountTable NVFS POSIX Dispatch Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mount_table_nvfs_posix_dispatch_spec

MountTable NVFS POSIX Dispatch Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/nvfs/mount_table_nvfs_posix_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

MountTable NVFS POSIX Dispatch Specification

Verifies that MountTable forwards mutating file operations through the
NvfsPosixDriver mount, not just longest-prefix resolution.

## Scenarios

### MountTable NVFS POSIX dispatch — mutating I/O

#### open + write + pread route through the /data NvfsPosix mount

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- open + write + pread route through the /data NvfsPosix mount
   - Expected: mt.pread(reopened, 0, 5).unwrap() equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("open + write + pread route through the /data NvfsPosix mount")
val mt = make_table()
val fh = mt.open("/data/hello.txt", OpenFlags.write_only().with_append().with_create()).unwrap()
mt.write(fh, "hello").unwrap()
mt.close(fh).unwrap()
val reopened = mt.open("/data/hello.txt", OpenFlags.read_only()).unwrap()
expect(mt.pread(reopened, 0, 5).unwrap()).to_equal("hello")
mt.close(reopened).unwrap()
```

</details>

#### rename stays within the NvfsPosix mount and preserves content

- rename stays within the NvfsPosix mount and preserves content
   - Expected: mt.pread(reopened, 0, 3).unwrap() equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rename stays within the NvfsPosix mount and preserves content")
val mt = make_table()
val fh = mt.open("/data/from.txt", OpenFlags.write_only().with_append().with_create()).unwrap()
mt.write(fh, "abc").unwrap()
mt.close(fh).unwrap()
mt.rename("/data/from.txt", "/data/to.txt").unwrap()
val reopened = mt.open("/data/to.txt", OpenFlags.read_only()).unwrap()
expect(mt.pread(reopened, 0, 3).unwrap()).to_equal("abc")
mt.close(reopened).unwrap()
```

</details>

#### ftruncate shrinks content through the NvfsPosix mount

- ftruncate shrinks content through the NvfsPosix mount
   - Expected: mt.pread(reopened, 0, 6).unwrap() equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ftruncate shrinks content through the NvfsPosix mount")
val mt = make_table()
val fh = mt.open("/data/trunc.txt", OpenFlags.write_only().with_append().with_create()).unwrap()
mt.write(fh, "abcdef").unwrap()
mt.ftruncate(fh, 3).unwrap()
mt.close(fh).unwrap()
val reopened = mt.open("/data/trunc.txt", OpenFlags.read_only()).unwrap()
expect(mt.pread(reopened, 0, 6).unwrap()).to_equal("abc")
mt.close(reopened).unwrap()
```

</details>

#### unlink removes the NvfsPosix-backed file

- unlink removes the NvfsPosix-backed file
   - Expected: mt.stat("/data/dead.txt").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unlink removes the NvfsPosix-backed file")
val mt = make_table()
val fh = mt.open("/data/dead.txt", OpenFlags.write_only().with_append().with_create()).unwrap()
mt.write(fh, "gone").unwrap()
mt.close(fh).unwrap()
mt.unlink("/data/dead.txt").unwrap()
expect(mt.stat("/data/dead.txt").is_err()).to_equal(true)
```

</details>

#### sibling non-/data paths still resolve to RamFs

- sibling non-/data paths still resolve to RamFs
   - Expected: resolved.mount_id.id equals `1`
   - Expected: resolved.relpath.raw equals `hosts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("sibling non-/data paths still resolve to RamFs")
val mt = make_table()
val resolved = mt.resolve(Path(raw: "/hosts")).unwrap()
expect(resolved.mount_id.id).to_equal(1)
expect(resolved.relpath.raw).to_equal("hosts")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5ff024605e44f4bf36bab9630144f26df142b94a8932c1338416cc42ea5d1041`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ff024605e44f4bf36bab9630144f26df142b94a8932c1338416cc42ea5d1041`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ff024605e44f4bf36bab9630144f26df142b94a8932c1338416cc42ea5d1041`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/storage/nvfs/mount_table_nvfs_posix_dispatch_spec.spl
mirror: doc/06_spec/02_integration/storage/nvfs/mount_table_nvfs_posix_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/nvfs/mount_table_nvfs_posix_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/nvfs/mount_table_nvfs_posix_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/nvfs/mount_table_nvfs_posix_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/storage/nvfs/mount_table_nvfs_posix_dispatch_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'open + write + pread route through the /data NvfsPosix mount' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/nvfs/mount_table_nvfs_posix_dispatch_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rename stays within the NvfsPosix mount and preserves content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/nvfs/mount_table_nvfs_posix_dispatch_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ftruncate shrinks content through the NvfsPosix mount' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
