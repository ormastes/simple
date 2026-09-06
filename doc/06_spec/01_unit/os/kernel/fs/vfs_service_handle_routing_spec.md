# VfsManager handle to mount routing — wiring spec

> longer a standalone data structure, it is the routing substrate of

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VfsManager handle to mount routing — wiring spec

longer a standalone data structure, it is the routing substrate of

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

longer a standalone data structure, it is the routing substrate of
`VfsManager`.

**Defect under test:** `VfsManager.read/write/close/seek`
(`src/os/services/vfs/vfs.spl`) used to route *every* handle to
`self.mounts[0]` ("Simplified: use first mount"), and `VfsService`
dispatch_read/write/close/seek reached into `self.vfs.mounts[0]` directly.
Filesystem drivers number handles privately from 1, so a file opened on
mount B was read, written, seeked and closed against mount A.

**Oracle — absolute, never a value against itself.** Each stub driver
stamps its own filesystem name into everything it returns:
`read` yields the bytes of `"<name>-payload"`, `write` returns a
name-derived code, `seek` returns a name-derived position, and `close`
reports `"close-routed-to-<name>"`. `"beta-payload"` can only have come
from mount B; every assertion is paired with the explicit negative that it
is *not* mount A's value.

## Scenarios

### VfsManager routes handle ops to the mount that opened them

#### registers the opening mount and returns a table handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### rolls back a driver open when global handle admission is exhausted

- fill every bounded global handle slot
- the open fails and reports the backend close rollback failure honestly
- no additional global handle or userspace fd is issued
   - Expected: vfs.open_handle_count() equals `VFS_HANDLE_TABLE_MAX_OPEN`
   - Expected: vfs.next_fd equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = two_mount_vfs()
var saturated: [VfsHandleEntry] = []
var i = 0
while i < VFS_HANDLE_TABLE_MAX_OPEN:
    saturated.push(VfsHandleEntry(
        active: true, retired: false, generation: 1u32,
        mount_index: 0, mount_path: "/alpha", driver_handle: (i + 1).to_u64()
    ))
    i = i + 1
vfs.handles = VfsHandleTable(
    entries: saturated, live_count: VFS_HANDLE_TABLE_MAX_OPEN)

step("fill every bounded global handle slot")
val opened = vfs.open("/beta/report.txt", rw_flags())

step("the open fails and reports the backend close rollback failure honestly")
expect(opened.is_err()).to_be(true)
expect(opened.unwrap_err()).to_contain("VFS handle table capacity exhausted")
expect(opened.unwrap_err()).to_contain("driver close rollback failed: close-routed-to-beta")

step("no additional global handle or userspace fd is issued")
expect(vfs.open_handle_count()).to_equal(VFS_HANDLE_TABLE_MAX_OPEN)
expect(vfs.next_fd).to_equal(3)
```

</details>

#### reads from mount B, not from mount A

- read returns beta's stamped payload
   - Expected: bytes_to_string(got.unwrap()) equals `beta-payload`
- negative: it is NOT alpha's payload (the mounts[0] answer)
   - Expected: bytes_to_string(alpha_read.unwrap()) equals `alpha-payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = two_mount_vfs()
val fd = vfs.open("/beta/report.txt", rw_flags()).unwrap()

step("read returns beta's stamped payload")
val got = vfs.read(fd.node, 32 as u64)
expect(got.is_ok()).to_be(true)
expect(bytes_to_string(got.unwrap())).to_equal("beta-payload")

step("negative: it is NOT alpha's payload (the mounts[0] answer)")
expect(bytes_to_string(got.unwrap())).to_contain("beta")
# Bind the open first: a mutating call nested inside another call's
# argument list loses the receiver's write (self-hosted defect).
val alpha_fd = vfs.open("/alpha/other.txt", rw_flags()).unwrap()
val alpha_read = vfs.read(alpha_fd.node, 32 as u64)
expect(bytes_to_string(alpha_read.unwrap())).to_equal("alpha-payload")
```

</details>

#### writes to mount B, not to mount A

- write returns beta's base code 2000 plus the byte count
   - Expected: wrote.unwrap() equals `2005 as u64`
- negative: alpha would have answered 1005
   - Expected: vfs.write(alpha_fd.node, string_to_bytes("abcde")).unwrap() equals `1005 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = two_mount_vfs()
val fd = vfs.open("/beta/report.txt", rw_flags()).unwrap()

step("write returns beta's base code 2000 plus the byte count")
val wrote = vfs.write(fd.node, string_to_bytes("abcde"))
expect(wrote.is_ok()).to_be(true)
expect(wrote.unwrap()).to_equal(2005 as u64)

step("negative: alpha would have answered 1005")
val alpha_fd = vfs.open("/alpha/other.txt", rw_flags()).unwrap()
expect(vfs.write(alpha_fd.node, string_to_bytes("abcde")).unwrap()).to_equal(1005 as u64)
```

</details>

#### seeks on mount B, not on mount A

- seek returns beta's base position 200 plus the offset
   - Expected: pos.unwrap() equals `207 as u64`
- negative: alpha would have answered 107
   - Expected: vfs.seek(alpha_fd.node, 7, SeekWhence.Set).unwrap() equals `107 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = two_mount_vfs()
val fd = vfs.open("/beta/report.txt", rw_flags()).unwrap()

step("seek returns beta's base position 200 plus the offset")
val pos = vfs.seek(fd.node, 7, SeekWhence.Set)
expect(pos.is_ok()).to_be(true)
expect(pos.unwrap()).to_equal(207 as u64)

step("negative: alpha would have answered 107")
val alpha_fd = vfs.open("/alpha/other.txt", rw_flags()).unwrap()
expect(vfs.seek(alpha_fd.node, 7, SeekWhence.Set).unwrap()).to_equal(107 as u64)
```

</details>

#### closes on mount B and retires the handle

- close is delivered to beta's driver
   - Expected: closed.unwrap_err() equals `close-routed-to-beta`
- the VFS handle is retired even though the driver reported an error
   - Expected: vfs.open_handle_count() equals `0`
- a replay is terminal success and cannot be re-routed to mount A
- a never-opened handle still fails rather than forging a receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = two_mount_vfs()
val fd = vfs.open("/beta/report.txt", rw_flags()).unwrap()
expect(vfs.open_handle_count()).to_equal(1)

step("close is delivered to beta's driver")
val closed = vfs.close(fd.node)
expect(closed.is_err()).to_be(true)
expect(closed.unwrap_err()).to_equal("close-routed-to-beta")

step("the VFS handle is retired even though the driver reported an error")
expect(vfs.open_handle_count()).to_equal(0)

step("a replay is terminal success and cannot be re-routed to mount A")
val again = vfs.close(fd.node)
expect(again.is_ok()).to_be(true)
expect(again.unwrap()).to_be(true)

step("a never-opened handle still fails rather than forging a receipt")
val unknown = vfs.close(999 as u64)
expect(unknown.is_err()).to_be(true)
expect(unknown.unwrap_err()).to_contain("unknown VFS handle")
```

</details>

#### keeps two same-numbered driver handles apart

- both drivers hand out driver handle 1 for their first open
   - Expected: vfs.handle_driver_handle(a.node) equals `vfs.handle_driver_handle(b.node)`
- but the VFS handles are distinct and resolve to different mounts
   - Expected: vfs.handle_mount_path(a.node) equals `/alpha`
   - Expected: vfs.handle_mount_path(b.node) equals `/beta`
- and the payloads follow the mount, not the shared driver handle
   - Expected: bytes_to_string(vfs.read(a.node, 32 as u64).unwrap()) equals `alpha-payload`
   - Expected: bytes_to_string(vfs.read(b.node, 32 as u64).unwrap()) equals `beta-payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("both drivers hand out driver handle 1 for their first open")
var vfs = two_mount_vfs()
val a = vfs.open("/alpha/one.txt", rw_flags()).unwrap()
val b = vfs.open("/beta/one.txt", rw_flags()).unwrap()
expect(vfs.handle_driver_handle(a.node)).to_equal(vfs.handle_driver_handle(b.node))

step("but the VFS handles are distinct and resolve to different mounts")
assert_true(a.node != b.node)
expect(vfs.handle_mount_path(a.node)).to_equal("/alpha")
expect(vfs.handle_mount_path(b.node)).to_equal("/beta")

step("and the payloads follow the mount, not the shared driver handle")
expect(bytes_to_string(vfs.read(a.node, 32 as u64).unwrap())).to_equal("alpha-payload")
expect(bytes_to_string(vfs.read(b.node, 32 as u64).unwrap())).to_equal("beta-payload")
```

</details>

#### rejects a handle whose mount was unmounted

- unmounting beta drops its open descriptions
   - Expected: vfs.open_handle_count() equals `0`
- the stale handle errors instead of falling through to alpha


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vfs = two_mount_vfs()
val fd = vfs.open("/beta/report.txt", rw_flags()).unwrap()

step("unmounting beta drops its open descriptions")
expect(vfs.unmount("/beta").is_ok()).to_be(true)
expect(vfs.open_handle_count()).to_equal(0)

step("the stale handle errors instead of falling through to alpha")
val stale = vfs.read(fd.node, 32 as u64)
expect(stale.is_err()).to_be(true)
expect(stale.unwrap_err()).to_contain("unknown VFS handle")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `c30bf1dc44e319f1f6f10ad1e8a5d602e769b54ea7e3670e8f7c58816c06b6d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c30bf1dc44e319f1f6f10ad1e8a5d602e769b54ea7e3670e8f7c58816c06b6d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c30bf1dc44e319f1f6f10ad1e8a5d602e769b54ea7e3670e8f7c58816c06b6d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.spl:133:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'registers the opening mount and returns a table handle' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.spl:154:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rolls back a driver open when global handle admission is exhausted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.spl:180:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads from mount B, not from mount A' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/vfs_service_handle_routing_spec.spl:198:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes to mount B, not to mount A' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
