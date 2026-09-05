# VFS chmod + symlink IPC Operations

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VFS chmod + symlink IPC Operations

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #B1 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/unit/os/services/vfs/vfs_chmod_symlink_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### VFS chmod routing

#### chmod routes to filesystem

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- chmod routes to filesystem
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chmod routes to filesystem")
var mgr = VfsManager.new()
val fs = MockFs.new()
mgr.mount("/", "mock", "", false, fs)
val result = mgr.chmod("/etc/foo", 0o755)
expect(result.is_ok()).to_equal(true)
```

</details>

#### chmod on a read-only mount returns error

- chmod on a read-only mount returns error
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chmod on a read-only mount returns error")
var mgr = VfsManager.new()
val fs = MockFs.new()
mgr.mount("/", "mock", "", true, fs)
val result = mgr.chmod("/etc/foo", 0o755)
expect(result.is_err()).to_equal(true)
```

</details>

### VFS symlink routing

#### symlink routes to filesystem

- symlink routes to filesystem
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("symlink routes to filesystem")
var mgr = VfsManager.new()
val fs = MockFs.new()
mgr.mount("/", "mock", "", false, fs)
val result = mgr.symlink("/usr/bin/sh", "/bin/sh")
expect(result.is_ok()).to_equal(true)
```

</details>

#### symlink on read-only mount returns error

- symlink on read-only mount returns error
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("symlink on read-only mount returns error")
var mgr = VfsManager.new()
val fs = MockFs.new()
mgr.mount("/", "mock", "", true, fs)
val result = mgr.symlink("/usr/bin/sh", "/bin/sh")
expect(result.is_err()).to_equal(true)
```

</details>

### VFS mutation argument routing

#### translates chmod paths beneath the selected mount

- translates chmod paths beneath the selected mount
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translates chmod paths beneath the selected mount")
var mgr = VfsManager.new()
mgr.mount("/containers/a", "mock", "", false, MutationArgumentFs.new())
val result = mgr.chmod("/containers/a/etc/tool", 0o755)
expect(result.is_ok()).to_equal(true)
```

</details>

#### preserves symlink target order while translating only its link path

- preserves symlink target order while translating only its link path
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves symlink target order while translating only its link path")
var mgr = VfsManager.new()
mgr.mount("/bin", "mock", "", false, MutationArgumentFs.new())
val result = mgr.symlink("/usr/bin/sh", "/bin/sh")
expect(result.is_ok()).to_equal(true)
```

</details>

### VFS mutation service ownership

#### delegates every mutation handler to the VfsManager

- delegates every mutation handler to the VfsManager


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("delegates every mutation handler to the VfsManager")
val source = read_file("src/os/services/vfs/vfs_service.spl")
expect(source).to_contain("match self.vfs.unlink(path):")
expect(source).to_contain("match self.vfs.rmdir(path):")
expect(source).to_contain("match self.vfs.rename(old_path, new_path):")
expect(source).to_contain("match self.vfs.chmod(path, mode):")
expect(source).to_contain("match self.vfs.symlink(target, link_path):")
```

</details>

### VFS rename mount boundaries

#### rejects renames that cross mounted filesystems

- rejects renames that cross mounted filesystems
   - Expected: result.is_err() is true
   - Expected: result.unwrap_err() equals `cross-mount rename is not supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects renames that cross mounted filesystems")
var mgr = VfsManager.new()
mgr.mount("/alpha", "mock", "", false, MockFs.new())
mgr.mount("/beta", "mock", "", false, MockFs.new())
val result = mgr.rename("/alpha/old", "/beta/new")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal("cross-mount rename is not supported")
```

</details>

#### does not treat a sibling prefix as a mounted path

- does not treat a sibling prefix as a mounted path
   - Expected: result.is_err() is true
   - Expected: result.unwrap_err() equals `no filesystem mounted for path: /alphabet/old`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat a sibling prefix as a mounted path")
var mgr = VfsManager.new()
mgr.mount("/alpha", "mock", "", false, MockFs.new())
val result = mgr.rename("/alphabet/old", "/alphabet/new")
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_equal("no filesystem mounted for path: /alphabet/old")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc78da69ed4f51ad423a2b547d3e49d7e3f70c153258c80ccb41abfe78fb58c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc78da69ed4f51ad423a2b547d3e49d7e3f70c153258c80ccb41abfe78fb58c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc78da69ed4f51ad423a2b547d3e49d7e3f70c153258c80ccb41abfe78fb58c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/services/vfs/vfs_chmod_symlink_spec.spl
mirror: doc/06_spec/unit/os/services/vfs/vfs_chmod_symlink_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/services/vfs/vfs_chmod_symlink_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/services/vfs/vfs_chmod_symlink_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/services/vfs/vfs_chmod_symlink_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chmod routes to filesystem' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/vfs/vfs_chmod_symlink_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chmod on a read-only mount returns error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/vfs/vfs_chmod_symlink_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'symlink routes to filesystem' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
