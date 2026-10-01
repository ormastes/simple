# Closing the `g_vfs_*` free-function bypass around the VFS container gate

> Lane CONTWIRE wired `VfsManager`'s path ops through one deny-wins gate (`enforce_lookup_grants`) and reported honestly that it left a hole: the `g_vfs_*` free functions in `vfs_write_ops.spl` / `vfs_init.spl` reach storage without ever consulting that gate. A deny-wins gate with an unguarded parallel entry point is not a gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Closing the `g_vfs_*` free-function bypass around the VFS container gate

Lane CONTWIRE wired `VfsManager`'s path ops through one deny-wins gate (`enforce_lookup_grants`) and reported honestly that it left a hole: the `g_vfs_*` free functions in `vfs_write_ops.spl` / `vfs_init.spl` reach storage without ever consulting that gate. A deny-wins gate with an unguarded parallel entry point is not a gate.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-CONTAINER #OS-VFS |
| Category | Security / Isolation |
| Difficulty | 4/5 |
| Status | In Progress |
| Source | `test/01_unit/os/services/vfs/vfs_bypass_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Lane CONTWIRE wired `VfsManager`'s path ops through one deny-wins gate
(`enforce_lookup_grants`) and reported honestly that it left a hole: the
`g_vfs_*` free functions in `vfs_write_ops.spl` / `vfs_init.spl` reach storage
without ever consulting that gate. A deny-wins gate with an unguarded parallel
entry point is not a gate.

Those free functions take no caller identity and cannot be given one today —
SimpleOS has no process-to-VfsManager binding. But they are not identity-free,
they are **ambient**: they act on behalf of whatever the global `g_vfs` is
currently resolving for. That ambient identity is exactly the one CONTWIRE
already gates. So the closure adds **no second gate** — every previously
bypassing function now asks `vfs_ambient_allows`, which forwards verbatim to
`VfsManager.enforce_lookup_grants`, which delegates the decision to
`container_view_allows_path`. One owner per decision, start to finish.

## What this spec can and cannot observe

Hosted storage drivers (DbFs, NvfsPosix) are **red at HEAD** in the interpreter
— `vfs_rootfs_porting_spec.spl` is 9 examples / 8 failures before this lane
touched anything, and `DbFsDriver.new_hosted()` fails outright. So "the write
landed on disk" is not observable here and is not claimed.

Two sinks ARE observable without storage, and both are used for genuine
end-to-end allow/deny evidence through the free-function API:

* `g_vfs_readdir` -> the ambient `VfsManager` -> a mounted mock filesystem;
* `g_vfs_read_executable_bytes` / `g_vfs_read_file_bytes` -> the in-memory app
  registry cache, which they consult BEFORE any driver. Serving cached
  executable bytes across a namespace boundary is precisely the escape being
  closed, so the gate is placed ahead of the cache and that is what is asserted.

The remaining functions are covered by the decision they consume (exact
operation string, exact path normalisation) plus a structural guard that fails
if a future edit removes the gate call. Nothing here fabricates a storage PASS.

## Scenarios

### host context is unchanged by the bypass closure

#### reports host context and permits every operation on every path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### still reaches the sink for readdir through the free function

- Host context, / mounted on a never-refusing filesystem
- g_vfs_readdir returns the mock's entries — the free function still works


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Host context, / mounted on a never-refusing filesystem")
_fresh_ambient_host_vfs()

step("g_vfs_readdir returns the mock's entries — the free function still works")
val entries = g_vfs_readdir("/")
assert_eq(entries.len(), 2)
```

</details>

#### still serves cached executable bytes through the free function

- Host context with a cached executable
- Both read entry points return the bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Host context with a cached executable")
_fresh_ambient_host_vfs()
app_registry_cache_bytes("/vbc/host_app", _some_bytes())

step("Both read entry points return the bytes")
assert_eq(g_vfs_read_executable_bytes("/vbc/host_app").len(), 4)
assert_eq(g_vfs_read_file_bytes("/vbc/host_app").len(), 4)
```

</details>

### a container cannot reach outside its root through the free functions

#### refuses reads of a host path that used to be served

- Cache an executable that lives outside the container's root
- Confine the ambient VFS to /containers/a
- The previously-bypassing read entry points now return nothing
- Leaving the container serves them again — the refusal was the gate, not a lost cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cache an executable that lives outside the container's root")
_fresh_ambient_host_vfs()
app_registry_cache_bytes("/vbc/host_app", _some_bytes())

step("Confine the ambient VFS to /containers/a")
vfs_ambient_enter_container("/containers/a", [101u64])
assert_true(vfs_ambient_in_container())

step("The previously-bypassing read entry points now return nothing")
assert_eq(g_vfs_read_executable_bytes("/vbc/host_app").len(), 0)
assert_eq(g_vfs_read_file_bytes("/vbc/host_app").len(), 0)
assert_eq(g_vfs_read_file_text("/vbc/host_app"), "")

step("Leaving the container serves them again — the refusal was the gate, not a lost cache")
vfs_ambient_leave_container()
assert_eq(g_vfs_read_executable_bytes("/vbc/host_app").len(), 4)
```

</details>

#### serves in-root reads for the container that owns them

- Cache an executable inside container A's root
- Container A reads it
- Container B is refused the SAME path


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cache an executable inside container A's root")
_fresh_ambient_host_vfs()
app_registry_cache_bytes("/containers/a/bin/app", _some_bytes())

step("Container A reads it")
vfs_ambient_enter_container("/containers/a", [101u64])
assert_eq(g_vfs_read_executable_bytes("/containers/a/bin/app").len(), 4)

step("Container B is refused the SAME path")
vfs_ambient_enter_container("/containers/b", [202u64])
assert_eq(g_vfs_read_executable_bytes("/containers/a/bin/app").len(), 0)
```

</details>

#### refuses readdir outside the root and permits it inside

- Confine to /containers/a
- Enumerating the host root yields nothing
- Enumerating inside the root still reaches the mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Confine to /containers/a")
_fresh_ambient_host_vfs()
vfs_ambient_enter_container("/containers/a", [101u64])

step("Enumerating the host root yields nothing")
assert_eq(g_vfs_readdir("/").len(), 0)

step("Enumerating inside the root still reaches the mock")
assert_eq(g_vfs_readdir("/containers/a/etc").len(), 2)
```

</details>

#### refuses the write-side free functions outside the root

- Confine to /containers/a
- Write, byte-write, delete and existence all fail closed for a host path
- And the decision each of them consumed is a genuine deny


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Confine to /containers/a")
_fresh_ambient_host_vfs()
vfs_ambient_enter_container("/containers/a", [101u64])

step("Write, byte-write, delete and existence all fail closed for a host path")
assert_false(g_vfs_write_file_text("/etc/shadow", "pwned"))
assert_false(g_vfs_write_file_bytes("/etc/shadow", _some_bytes()))
assert_false(g_vfs_delete_file("/etc/shadow"))
assert_false(g_vfs_file_exists("/etc/shadow"))
assert_true(g_vfs_file_size("/etc/shadow") == nil)

step("And the decision each of them consumed is a genuine deny")
assert_true(vfs_ambient_enforce("write", "/etc/shadow").is_err())
assert_true(vfs_ambient_enforce("unlink", "/etc/shadow").is_err())
assert_true(vfs_ambient_enforce("stat", "/etc/shadow").is_err())
```

</details>

#### refuses traversal without normalising it

- Confine to /containers/a and try to climb out


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Confine to /containers/a and try to climb out")
_fresh_ambient_host_vfs()
vfs_ambient_enter_container("/containers/a", [101u64])
assert_false(vfs_ambient_allows("read", "/containers/a/../b/secret"))
assert_eq(g_vfs_readdir("/containers/a/../..").len(), 0)
assert_false(g_vfs_write_file_text("/containers/a/../b/x", "y"))
```

</details>

#### normalises a bare name to an absolute path before deciding

- Bare names are what the FAT32-era callers pass
- A bare name resolves at / and is therefore outside the root — refused, not silently allowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bare names are what the FAT32-era callers pass")
_fresh_ambient_host_vfs()
vfs_ambient_enter_container("/containers/a", [101u64])

step("A bare name resolves at / and is therefore outside the root — refused, not silently allowed")
assert_false(g_vfs_file_exists("SHADOW.TXT"))
assert_false(g_vfs_write_file_text("SHADOW.TXT", "pwned"))
```

</details>

### a stopped container fails closed through the free functions

#### resolves nothing under the rootless view a stopped container holds

- Cache bytes, then enter the rootless view sys_stop leaves behind
- Nothing resolves — not even its own former root


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cache bytes, then enter the rootless view sys_stop leaves behind")
_fresh_ambient_host_vfs()
app_registry_cache_bytes("/containers/a/bin/app", _some_bytes())
vfs_ambient_enter_container_view(container_view_rootless())

step("Nothing resolves — not even its own former root")
assert_true(vfs_ambient_in_container())
assert_eq(g_vfs_read_executable_bytes("/containers/a/bin/app").len(), 0)
assert_eq(g_vfs_readdir("/containers/a").len(), 0)
assert_false(g_vfs_write_file_text("/containers/a/x", "y"))
assert_false(g_vfs_file_exists("/containers/a/bin/app"))
```

</details>

#### treats the explicit rootless entry point the same way

- The convenience entry point must not be a softer door


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("The convenience entry point must not be a softer door")
_fresh_ambient_host_vfs()
vfs_ambient_enter_rootless_container()
assert_false(vfs_ambient_allows("read", "/"))
assert_eq(g_vfs_readdir("/").len(), 0)
```

</details>

### namespace construction is refused wholesale inside a container

#### refuses removable mount and unmount while confined

- Confine the ambient VFS
- Both refuse before touching any device


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Confine the ambient VFS")
_fresh_ambient_host_vfs()
vfs_ambient_enter_container("/containers/a", [101u64])
assert_true(vfs_ambient_in_container())

step("Both refuse before touching any device")
assert_false(vfs_mount_removable(0u64, "/containers/a/mnt"))
assert_false(vfs_unmount_removable("/containers/a/mnt"))
```

</details>

#### does not arm that guard in host context

- The guard is a single predicate; in host context it is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("The guard is a single predicate; in host context it is false")
_fresh_ambient_host_vfs()
assert_false(vfs_ambient_in_container())
```

</details>

### the closure is structural, not incidental

#### keeps the ambient gate call in every previously-bypassing write op

- Read the write-ops source
- Each public storage-reaching entry point consults the ambient gate
- The unauthenticated cursor-write helper is gone, not merely unexported


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the write-ops source")
val src = read_file("src/os/services/vfs/vfs_write_ops.spl")

step("Each public storage-reaching entry point consults the ambient gate")
assert_contains(src, "vfs_ambient_allows(\"write\"")
assert_contains(src, "vfs_ambient_allows(\"unlink\"")
assert_contains(src, "vfs_ambient_allows(\"stat\"")
assert_contains(src, "vfs_ambient_in_container()")

step("The unauthenticated cursor-write helper is gone, not merely unexported")
assert_false(src.contains("fn g_vfs_write_selected_file_text"))
```

</details>

#### keeps the ambient gate call in every previously-bypassing read op

- Read the init-hub source
- Reads and size checks consult the ambient gate
- The duplicated path helpers are gone — one owner for that arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the init-hub source")
val src = read_file("src/os/services/vfs/vfs_init.spl")

step("Reads and size checks consult the ambient gate")
assert_contains(src, "vfs_ambient_allows(\"read\"")
assert_contains(src, "vfs_ambient_allows(\"stat\"")

step("The duplicated path helpers are gone — one owner for that arithmetic")
assert_false(src.contains("fn g_vfs_abs_path(name: text) -> Path:"))
assert_false(src.contains("fn g_vfs_root_path(name: text) -> text:"))
```

</details>

#### adds no second policy — the decision still belongs to the kernel primitive

- Read the ambient accessors
- They forward to the converged choke point and decide nothing themselves


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the ambient accessors")
val src = (read_file("src/os/services/vfs/vfs_boot_init.spl") + read_file("src/os/services/vfs/vfs_boot_core.spl") + read_file("src/os/services/vfs/vfs_boot_state.spl") + read_file("src/os/services/vfs/vfs_ambient_context.spl") + read_file("src/os/services/vfs/nvme_boot_runtime_owner.spl") + read_file("src/os/services/vfs/nvme_filesystem_direct_io.spl") + read_file("src/os/services/vfs/nvme_q35_lease_perf.spl") + read_file("src/os/services/vfs/direct_fat32_boot_reader.spl"))

step("They forward to the converged choke point and decide nothing themselves")
assert_contains(src, "g_vfs.enforce_lookup_grants(operation, path)")
assert_false(src.contains("fn vfs_ambient_root_of"))
assert_false(src.contains("starts_with(view.root"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `8c0b0a5985368458b22728563777293c3c368de7aad19748f362cabf00100bf8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c0b0a5985368458b22728563777293c3c368de7aad19748f362cabf00100bf8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c0b0a5985368458b22728563777293c3c368de7aad19748f362cabf00100bf8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/os/services/vfs/vfs_bypass_closure_spec.spl
mirror: doc/06_spec/01_unit/os/services/vfs/vfs_bypass_closure_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/vfs/vfs_bypass_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/vfs/vfs_bypass_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/vfs/vfs_bypass_closure_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/services/vfs/vfs_bypass_closure_spec.spl:168:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reports host context and permits every operation on every path' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/services/vfs/vfs_bypass_closure_spec.spl:185:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still reaches the sink for readdir through the free function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/vfs/vfs_bypass_closure_spec.spl:194:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still serves cached executable bytes through the free function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/vfs/vfs_bypass_closure_spec.spl:211:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses reads of a host path that used to be served' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
