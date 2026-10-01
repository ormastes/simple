# VFS handle to mount association — contract spec

> description table.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VFS handle to mount association — contract spec

description table.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/fs/handle_mount_association_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

description table.

**Defect under test:** `VfsManager.read/write/close/seek`
(`src/os/services/vfs/vfs.spl`) route every handle to `self.mounts[0]`,
documented in the source itself as *"Simplified: use first mount"*. Each
filesystem driver keeps a private handle namespace starting at 1, so with
two mounts the *same* handle value `1` exists on both — and the mounts[0]
route silently reads mount A's file when the caller opened a file on
mount B.

The oracle here is absolute, never a value compared to itself: each mock
driver stamps its own filesystem name onto the bytes it returns, so
`"winfs:beta-payload"` can only have come from mount B and
`"rootfs:alpha-payload"` can only have come from mount A.

## Scenarios

### VFS handle to mount association

#### gives colliding driver handles distinct VFS handles

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gives colliding driver handles distinct VFS handles
- open one file on each of two mounts
- both drivers issued driver-local handle 1 — the collision
   - Expected: fx.drv_a equals `1 as u64`
   - Expected: fx.drv_b equals `1 as u64`
- the VFS handles are still distinct
   - Expected: fx.table.open_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("gives colliding driver handles distinct VFS handles")
step("open one file on each of two mounts")
val fx = make_fixture()

step("both drivers issued driver-local handle 1 — the collision")
expect(fx.drv_a).to_equal(1 as u64)
expect(fx.drv_b).to_equal(1 as u64)

step("the VFS handles are still distinct")
expect(fx.h_a).to_be_greater_than(0u64)
expect(fx.h_b).to_be_greater_than(fx.h_a)
expect(fx.table.open_count()).to_equal(2)
```

</details>

#### resolves a handle opened on mount B to mount B

- resolves a handle opened on mount B to mount B
- handle B carries mount index 1 and mount path /win
   - Expected: fx.table.mount_index_of(fx.h_b) equals `1`
   - Expected: fx.table.mount_path_of(fx.h_b) equals `/win`
- and unwraps back to the driver-local handle B issued
   - Expected: fx.table.driver_handle_of(fx.h_b) equals `1 as u64`
- handle A still resolves to mount A
   - Expected: fx.table.mount_index_of(fx.h_a) equals `0`
   - Expected: fx.table.mount_path_of(fx.h_a) equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("resolves a handle opened on mount B to mount B")
val fx = make_fixture()

step("handle B carries mount index 1 and mount path /win")
expect(fx.table.mount_index_of(fx.h_b)).to_equal(1)
expect(fx.table.mount_path_of(fx.h_b)).to_equal("/win")

step("and unwraps back to the driver-local handle B issued")
expect(fx.table.driver_handle_of(fx.h_b)).to_equal(1 as u64)

step("handle A still resolves to mount A")
expect(fx.table.mount_index_of(fx.h_a)).to_equal(0)
expect(fx.table.mount_path_of(fx.h_a)).to_equal("/")
```

</details>

#### reads mount B content through a handle opened on mount B

- reads mount B content through a handle opened on mount B
- read via the handle to mount association
   - Expected: route_read(fx, fx.h_b) equals `winfs:beta-payload`
- the mount A handle reads mount A content
   - Expected: route_read(fx, fx.h_a) equals `rootfs:alpha-payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reads mount B content through a handle opened on mount B")
val fx = make_fixture()

step("read via the handle to mount association")
expect(route_read(fx, fx.h_b)).to_equal("winfs:beta-payload")

step("the mount A handle reads mount A content")
expect(route_read(fx, fx.h_a)).to_equal("rootfs:alpha-payload")
```

</details>

#### never lets a mount B handle reach mount A

- never lets a mount B handle reach mount A
- negative: the B handle must NOT produce mount A bytes
- control: the pre-fix mounts[0] route DOES produce mount A bytes
   - Expected: first_mount_read(fx, fx.drv_b) equals `rootfs:alpha-payload`
- so the two routes disagree — the fix is load bearing


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("never lets a mount B handle reach mount A")
val fx = make_fixture()

step("negative: the B handle must NOT produce mount A bytes")
val routed = route_read(fx, fx.h_b)
assert_true(routed != "rootfs:alpha-payload")
assert_true(routed != "rootfs:ENOENT")

step("control: the pre-fix mounts[0] route DOES produce mount A bytes")
expect(first_mount_read(fx, fx.drv_b)).to_equal("rootfs:alpha-payload")

step("so the two routes disagree — the fix is load bearing")
assert_true(routed != first_mount_read(fx, fx.drv_b))
```

</details>

#### invalidates a handle on close and leaves the sibling open

- invalidates a handle on close and leaves the sibling open
- close the mount B handle
- it no longer resolves to any mount
   - Expected: fx.table.is_open(fx.h_b) is false
   - Expected: fx.table.mount_index_of(fx.h_b) equals `VFS_HANDLE_NO_MOUNT`
   - Expected: route_read(fx, fx.h_b) equals `EBADF`
- double close is reported, not silently accepted
   - Expected: fx.table.release(fx.h_b) is false
- the mount A handle is untouched
   - Expected: route_read(fx, fx.h_a) equals `rootfs:alpha-payload`
   - Expected: fx.table.open_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("invalidates a handle on close and leaves the sibling open")
var fx = make_fixture()

step("close the mount B handle")
assert_true(fx.table.release(fx.h_b))

step("it no longer resolves to any mount")
expect(fx.table.is_open(fx.h_b)).to_equal(false)
expect(fx.table.mount_index_of(fx.h_b)).to_equal(VFS_HANDLE_NO_MOUNT)
expect(route_read(fx, fx.h_b)).to_equal("EBADF")

step("double close is reported, not silently accepted")
expect(fx.table.release(fx.h_b)).to_equal(false)

step("the mount A handle is untouched")
expect(route_read(fx, fx.h_a)).to_equal("rootfs:alpha-payload")
expect(fx.table.open_count()).to_equal(1)
```

</details>

#### keeps handles pointing at their filesystem after an unmount renumbers mounts

- keeps handles pointing at their filesystem after an unmount renumbers mounts
- unmount index 0 — VfsManager does mounts.remove(0)
   - Expected: fx.table.release_mount(0) equals `1`
- the surviving mount B handle now names index 0, still path /win
   - Expected: fx.table.mount_index_of(fx.h_b) equals `0`
   - Expected: fx.table.mount_path_of(fx.h_b) equals `/win`
   - Expected: fx.table.open_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps handles pointing at their filesystem after an unmount renumbers mounts")
var fx = make_fixture()

step("unmount index 0 — VfsManager does mounts.remove(0)")
expect(fx.table.release_mount(0)).to_equal(1)
fx.table.reindex_after_unmount(0)

step("the surviving mount B handle now names index 0, still path /win")
expect(fx.table.mount_index_of(fx.h_b)).to_equal(0)
expect(fx.table.mount_path_of(fx.h_b)).to_equal("/win")
expect(fx.table.open_count()).to_equal(1)
```

</details>

#### rejects a handle that was never issued

- rejects a handle that was never issued
- an unknown handle resolves to no mount
   - Expected: fx.table.is_open(999 as u64) is false
   - Expected: fx.table.mount_index_of(999 as u64) equals `VFS_HANDLE_NO_MOUNT`
   - Expected: route_read(fx, 999 as u64) equals `EBADF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a handle that was never issued")
val fx = make_fixture()

step("an unknown handle resolves to no mount")
expect(fx.table.is_open(999 as u64)).to_equal(false)
expect(fx.table.mount_index_of(999 as u64)).to_equal(VFS_HANDLE_NO_MOUNT)
expect(route_read(fx, 999 as u64)).to_equal("EBADF")
```

</details>

#### rejects invalid owner identities before mutating the table

- rejects invalid owner identities before mutating the table
- negative mount indices and zero driver handles are never admitted
- ambiguous and traversal-bearing mount paths are never persisted
- all rejected admissions leave capacity and ID state untouched
   - Expected: table.open_count() equals `0`
   - Expected: table.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects invalid owner identities before mutating the table")
var table = VfsHandleTable.new()

step("negative mount indices and zero driver handles are never admitted")
expect(table.register(-1, "/", 1u64).is_err()).to_be(true)
expect(table.register(0, "/", 0u64).is_err()).to_be(true)

step("ambiguous and traversal-bearing mount paths are never persisted")
expect(table.register(0, "relative", 1u64).is_err()).to_be(true)
expect(table.register(0, "/safe/../escape", 1u64).is_err()).to_be(true)
expect(table.register(0, "/safe//child", 1u64).is_err()).to_be(true)
expect(table.register(0, "/safe/", 1u64).is_err()).to_be(true)

step("all rejected admissions leave capacity and ID state untouched")
expect(table.open_count()).to_equal(0)
expect(table.entries.len()).to_equal(0)
```

</details>

#### retires a terminal-generation slot instead of wrapping it

- retires a terminal-generation slot instead of wrapping it
- release invalidates the handle without incrementing generation
- the retired slot is skipped and a distinct slot is admitted
   - Expected: table.driver_handle_of(replacement.unwrap()) equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("retires a terminal-generation slot instead of wrapping it")
val terminal_handle = (VFS_HANDLE_GENERATION_MAX.to_u64() << 32) | 1u64
var table = VfsHandleTable(entries: [VfsHandleEntry(
    active: true, retired: false, generation: VFS_HANDLE_GENERATION_MAX,
    mount_index: 0, mount_path: "/", driver_handle: 1u64
)], live_count: 1)

step("release invalidates the handle without incrementing generation")
expect(table.release(terminal_handle)).to_be(true)
expect(table.is_open(terminal_handle)).to_be(false)
expect(table.was_issued(terminal_handle)).to_be(true)

step("the retired slot is skipped and a distinct slot is admitted")
val replacement = table.register(0, "/", 2u64)
expect(replacement.is_ok()).to_be(true)
expect(table.driver_handle_of(replacement.unwrap())).to_equal(2u64)
expect(table.entries[0].retired).to_be(true)
```

</details>

#### rejects a stale handle after its slot is reused

- rejects a stale handle after its slot is reused
- release advances the slot generation
- the next admission reuses the bounded slot with a new handle
   - Expected: table.entries.len() equals `1`
- the stale generation cannot resolve or release the new owner
   - Expected: table.mount_index_of(current) equals `1`
   - Expected: table.driver_handle_of(current) equals `22u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a stale handle after its slot is reused")
var table = VfsHandleTable.new()
val stale = table.register(0, "/", 11u64).unwrap()

step("release advances the slot generation")
expect(table.release(stale)).to_be(true)
expect(table.is_open(stale)).to_be(false)

step("the next admission reuses the bounded slot with a new handle")
val current = table.register(1, "/next", 22u64).unwrap()
expect(table.entries.len()).to_equal(1)

step("the stale generation cannot resolve or release the new owner")
expect(table.lookup(stale).found).to_be(false)
expect(table.release(stale)).to_be(false)
expect(table.was_issued(stale)).to_be(true)
expect(table.mount_index_of(current)).to_equal(1)
expect(table.driver_handle_of(current)).to_equal(22u64)
```

</details>

#### bounds live open-file descriptions without evicting an owner

- bounds live open-file descriptions without evicting an owner
- one more open fails rather than evicting or aliasing a live owner
   - Expected: rejected.unwrap_err() equals `VFS handle table capacity exhausted`
   - Expected: table.open_count() equals `VFS_HANDLE_TABLE_MAX_OPEN`
   - Expected: table.driver_handle_of(first_handle) equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("bounds live open-file descriptions without evicting an owner")
var table = VfsHandleTable.new()
var i = 0
var all_admitted = true
var first_handle = 0u64
while i < VFS_HANDLE_TABLE_MAX_OPEN:
    val admitted = table.register(0, "/", (i + 1) as u64)
    if admitted.is_err():
        all_admitted = false
    else:
        if i == 0:
            first_handle = admitted.unwrap()
    i = i + 1
expect(all_admitted).to_be(true)

step("one more open fails rather than evicting or aliasing a live owner")
val rejected = table.register(0, "/", 5000u64)
expect(rejected.is_err()).to_be(true)
expect(rejected.unwrap_err()).to_equal("VFS handle table capacity exhausted")
expect(table.open_count()).to_equal(VFS_HANDLE_TABLE_MAX_OPEN)
expect(table.driver_handle_of(first_handle)).to_equal(1u64)
```

</details>

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fdf5d6449a2711b5060f2c40d5c4d8f89178e406c9a6ace63a4a2b72e58ae198`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fdf5d6449a2711b5060f2c40d5c4d8f89178e406c9a6ace63a4a2b72e58ae198`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fdf5d6449a2711b5060f2c40d5c4d8f89178e406c9a6ace63a4a2b72e58ae198`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/fs/handle_mount_association_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/fs/handle_mount_association_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/fs/handle_mount_association_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/fs/handle_mount_association_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/fs/handle_mount_association_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/fs/handle_mount_association_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives colliding driver handles distinct VFS handles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/handle_mount_association_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a handle opened on mount B to mount B' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/fs/handle_mount_association_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads mount B content through a handle opened on mount B' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
