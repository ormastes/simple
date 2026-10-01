# @manual: primary

> Purpose: Prove that escape/path: traversal out of the container root is refused.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that escape/path: traversal out of the container root is refused.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-CTR-MDSOC |
| Category | Security / OS / Container |
| Status | In Progress |
| Design | doc/04_architecture/os/container/podman_mdsoc_container_arch.md |
| Source | `test/01_unit/os/services/container/container_escape_suite_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that escape/path: traversal out of the container root is refused.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-SERVICES-001
doc/01_research/local/REQ-OS-SERVICES-001.md
doc/03_plan/sys_test/REQ-OS-SERVICES-001.md
doc/04_architecture/REQ-OS-SERVICES-001.md
doc/05_design/REQ-OS-SERVICES-001.md

## Scenarios

### escape/path: traversal out of the container root is refused

#### a .. component in a resolved path is denied, never normalized away

- Verify: a .. component in a resolved path is denied, never normalized away
   - Expected: container_view_path_decision(v, "/containers/victim/../../etc/shadow") equals `deny`
   - Expected: container_view_path_decision(v, "/containers/victim/..") equals `deny`
   - Expected: container_view_path_decision(v, "/containers/victim/a/../../../etc") equals `deny`
   - Expected: container_view_path_decision(v, "/containers/victim/app/bin") equals `allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a .. component in a resolved path is denied, never normalized away")
val v = container_view_create("/containers/victim", [100u64])
expect(container_view_path_decision(v, "/containers/victim/../../etc/shadow")).to_equal("deny")
expect(container_view_path_decision(v, "/containers/victim/..")).to_equal("deny")
expect(container_view_path_decision(v, "/containers/victim/a/../../../etc")).to_equal("deny")
# ...while the legitimate path inside the root still resolves, so the
# oracle is not trivially "deny everything".
expect(container_view_path_decision(v, "/containers/victim/app/bin")).to_equal("allow")
```

</details>

#### an absolute host path outside the root is denied

- Verify: an absolute host path outside the root is denied
   - Expected: container_view_path_decision(v, "/etc/shadow") equals `deny`
   - Expected: container_view_path_decision(v, "/") equals `deny`
   - Expected: container_view_path_decision(v, "/proc/1/root") equals `deny`
   - Expected: container_view_path_decision(v, "/sys/firmware") equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: an absolute host path outside the root is denied")
val v = container_view_create("/containers/victim", [100u64])
expect(container_view_path_decision(v, "/etc/shadow")).to_equal("deny")
expect(container_view_path_decision(v, "/")).to_equal("deny")
expect(container_view_path_decision(v, "/proc/1/root")).to_equal("deny")
expect(container_view_path_decision(v, "/sys/firmware")).to_equal("deny")
```

</details>

#### a sibling path that merely CONTAINS the root as a prefix is denied

- Verify: a sibling path that merely CONTAINS the root as a prefix is denied
   - Expected: container_view_path_decision(v, "/rootfsevil/x") equals `deny`
   - Expected: container_view_path_decision(v, "/rootfs-backup/x") equals `deny`
   - Expected: container_view_path_decision(v, "/rootfs.old") equals `deny`
   - Expected: container_view_path_decision(v, "/rootfs") equals `allow`
   - Expected: container_view_path_decision(v, "/rootfs/x") equals `allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a sibling path that merely CONTAINS the root as a prefix is denied")
# Prefix confusion: "/rootfsevil" shares its first 8 characters with
# "/rootfs" but is a DIFFERENT directory. A naive starts_with(root)
# check hands the attacker the host filesystem.
val v = container_view_create("/rootfs", [100u64])
expect(container_view_path_decision(v, "/rootfsevil/x")).to_equal("deny")
expect(container_view_path_decision(v, "/rootfs-backup/x")).to_equal("deny")
expect(container_view_path_decision(v, "/rootfs.old")).to_equal("deny")
# the boundary itself and everything genuinely below it still resolve.
expect(container_view_path_decision(v, "/rootfs")).to_equal("allow")
expect(container_view_path_decision(v, "/rootfs/x")).to_equal("allow")
```

</details>

#### an OCI mount destination that escapes the root is rejected by name

- Verify: an OCI mount destination that escapes the root is rejected by name
   - Expected: r.ok is false
   - Expected: r.spec.root equals ``
   - Expected: r.spec.caps.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: an OCI mount destination that escapes the root is rejected by name")
val r = oci_import_checked(
    hostile_oci([OciMount(src: "tmpfs", dest: "/tmp/../../etc", mtype: "tmpfs")], ["cap.fs_read"], "/containers/evil", false),
    locked_policy()
)
expect(r.ok).to_equal(false)
expect(r.error).to_contain("escapes container root")
# a rejected import yields an EMPTY spec — no partial authority leaks.
expect(r.spec.root).to_equal("")
expect(r.spec.caps.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### an OCI mount SOURCE that escapes the bundle is rejected

- Verify: an OCI mount SOURCE that escapes the bundle is rejected
   - Expected: r.ok is false
   - Expected: r.spec.root equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: an OCI mount SOURCE that escapes the bundle is rejected")
# HOLE FOUND BY THIS SUITE (now fixed): only `dest` was checked for
# "..", and the raw-host-mount check only caught ABSOLUTE sources — so
# a RELATIVE traversal source walked through every 6.3 check.
val r = oci_import_checked(
    hostile_oci([OciMount(src: "../../../etc", dest: "/cfg", mtype: "bind")], ["cap.fs_read"], "/containers/evil", false),
    locked_policy()
)
expect(r.ok).to_equal(false)
expect(r.error).to_contain("source escapes the bundle")
expect(r.spec.root).to_equal("")
```

</details>

#### an OCI container root of slash, empty, or dot-dot is rejected

- Verify: an OCI container root of slash, empty, or dot-dot is rejected
   - Expected: r_slash.ok is false
   - Expected: r_slash.spec.root equals ``
   - Expected: r_empty.ok is false
   - Expected: r_dots.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: an OCI container root of slash, empty, or dot-dot is rejected")
# HOLE FOUND BY THIS SUITE (now fixed): root_path was copied verbatim
# into ContainerSpec.root, so an untrusted bundle could name the HOST
# root and container_view_create would confine the container to "/".
val p = locked_policy()
val r_slash = oci_import_checked(hostile_oci([], ["cap.fs_read"], "/", false), p)
expect(r_slash.ok).to_equal(false)
expect(r_slash.error).to_contain("root_path")
expect(r_slash.spec.root).to_equal("")

val r_empty = oci_import_checked(hostile_oci([], ["cap.fs_read"], "", false), p)
expect(r_empty.ok).to_equal(false)
expect(r_empty.error).to_contain("root_path")

val r_dots = oci_import_checked(hostile_oci([], ["cap.fs_read"], "../../..", false), p)
expect(r_dots.ok).to_equal(false)
expect(r_dots.error).to_contain("root_path")
```

</details>

### escape/caps: authority can never be amplified

#### an OCI config cannot import a capability outside the policy ceiling

- Verify: an OCI config cannot import a capability outside the policy ceiling
   - Expected: r.ok is true
   - Expected: r.spec.caps.len() equals `1`
   - Expected: r.spec.caps[0] equals `cap.fs_read`
   - Expected: caps_is_subset(["cap.sys_admin"], r.spec.caps) is false
   - Expected: caps_is_subset(["cap.kernel_module"], r.spec.caps) is false
   - Expected: caps_is_subset(["cap.raw_io"], r.spec.caps) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: an OCI config cannot import a capability outside the policy ceiling")
val r = oci_import_checked(
    hostile_oci([], ["cap.fs_read", "cap.sys_admin", "cap.kernel_module", "cap.raw_io"], "/containers/evil", false),
    locked_policy()
)
expect(r.ok).to_equal(true)
# Only the ceiling-approved cap survives — absolute oracle on the set.
expect(r.spec.caps.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(r.spec.caps[0]).to_equal("cap.fs_read")
expect(caps_is_subset(["cap.sys_admin"], r.spec.caps)).to_equal(false)
expect(caps_is_subset(["cap.kernel_module"], r.spec.caps)).to_equal(false)
expect(caps_is_subset(["cap.raw_io"], r.spec.caps)).to_equal(false)
```

</details>

#### a spawn request never carries a capability the container was not granted

- Verify: a spawn request never carries a capability the container was not granted
   - Expected: caps_is_subset(req.caps, w.granted_of(victim)) is true
   - Expected: caps_is_subset(["cap.sys_admin"], req.caps) is false
   - Expected: caps_is_subset(["cap.host_net"], req.caps) is false
   - Expected: req.isolation equals `container`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a spawn request never carries a capability the container was not granted")
var w = ContainerWorld.new()
val victim = w.sys_create("victim", "/containers/victim", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val req: SpawnRequest = w.sys_start(victim)
expect(caps_is_subset(req.caps, w.granted_of(victim))).to_equal(true)
expect(caps_is_subset(["cap.sys_admin"], req.caps)).to_equal(false)
expect(caps_is_subset(["cap.host_net"], req.caps)).to_equal(false)
expect(req.isolation).to_equal("container")
```

</details>

<details>
<summary>Advanced: a crash-loop restart cannot re-request caps beyond the create-time ceiling</summary>

#### a crash-loop restart cannot re-request caps beyond the create-time ceiling

- Verify: a crash-loop restart cannot re-request caps beyond the create-time ceiling
   - Expected: w.sys_monitor() equals `1`
   - Expected: w.granted_of(c).len() equals `0`
   - Expected: w.granted_of(c).len() equals `1`
   - Expected: w.granted_of(c)[0] equals `cap.fs_read`
   - Expected: caps_is_subset(["cap.sys_admin"], again.caps) is false
   - Expected: caps_is_subset(["cap.host_net"], again.caps) is false
   - Expected: caps_is_subset(again.caps, w.ceiling_of(c)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a crash-loop restart cannot re-request caps beyond the create-time ceiling")
# HOLE FOUND BY THIS SUITE (now fixed): section 21 empties the pouch on
# exit, so granted_caps could not bound the RE-acquisition —
# sys_restart took whatever the caller named. A container that crashes
# on purpose could come back holding cap.sys_admin.
var w = ContainerWorld.new()
val c = w.sys_create("victim", "/containers/victim", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
w.set_restart_policy(c, "on-failure", 3)
val first: SpawnRequest = w.sys_start(c)
w.post_monitor_report(c, "crashed", 137)
expect(w.sys_monitor()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(w.granted_of(c).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
# the attack: come back asking for far more than was ever granted.
val again: SpawnRequest = w.sys_restart(c, ["cap.fs_read", "cap.sys_admin", "cap.host_net"], "/containers/victim", [100u64], 1024u64, 4096u64, 100u64, 64u64)
expect(w.granted_of(c).len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(w.granted_of(c)[0]).to_equal("cap.fs_read")
expect(caps_is_subset(["cap.sys_admin"], again.caps)).to_equal(false)
expect(caps_is_subset(["cap.host_net"], again.caps)).to_equal(false)
expect(caps_is_subset(again.caps, w.ceiling_of(c))).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: a crash-loop restart cannot widen the container root to the host</summary>

#### a crash-loop restart cannot widen the container root to the host

- Verify: a crash-loop restart cannot widen the container root to the host
   - Expected: w.sys_monitor() equals `1`
   - Expected: w.path_decision(c, "/etc/shadow") equals `deny`
   - Expected: w.path_decision(c, "/") equals `deny`
   - Expected: w.path_decision(c, "/containers/victim/app") equals `allow`
   - Expected: w.ceiling_root_of(c) equals `/containers/victim`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a crash-loop restart cannot widen the container root to the host")
var w = ContainerWorld.new()
val c = w.sys_create("victim", "/containers/victim", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
w.set_restart_policy(c, "always", 3)
val first: SpawnRequest = w.sys_start(c)
w.post_monitor_report(c, "crashed", 9)
expect(w.sys_monitor()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val again: SpawnRequest = w.sys_restart(c, ["cap.fs_read"], "/", [100u64], 1024u64, 4096u64, 100u64, 64u64)
expect(w.path_decision(c, "/etc/shadow")).to_equal("deny")
expect(w.path_decision(c, "/")).to_equal("deny")
# clamped back to exactly the create-time root, which still works.
expect(w.path_decision(c, "/containers/victim/app")).to_equal("allow")
expect(w.ceiling_root_of(c)).to_equal("/containers/victim")
```

</details>


</details>

#### a restart may NARROW its root, proving the clamp is not a blanket reset

- Verify: a restart may NARROW its root, proving the clamp is not a blanket reset
   - Expected: w.sys_monitor() equals `1`
   - Expected: w.path_decision(c, "/containers/victim/inner/x") equals `allow`
   - Expected: w.path_decision(c, "/containers/victim/other") equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a restart may NARROW its root, proving the clamp is not a blanket reset")
var w = ContainerWorld.new()
val c = w.sys_create("victim", "/containers/victim", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
w.set_restart_policy(c, "always", 3)
val first: SpawnRequest = w.sys_start(c)
w.post_monitor_report(c, "exited", 0)
expect(w.sys_monitor()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val again: SpawnRequest = w.sys_restart(c, ["cap.fs_read"], "/containers/victim/inner", [100u64], 1024u64, 4096u64, 100u64, 64u64)
expect(w.path_decision(c, "/containers/victim/inner/x")).to_equal("allow")
# narrowed: the parent is now OUTSIDE this instance's view.
expect(w.path_decision(c, "/containers/victim/other")).to_equal("deny")
```

</details>

#### a pod member cannot inherit another pod member's capabilities

- Verify: a pod member cannot inherit another pod member's capabilities
   - Expected: w.granted_of(weak).len() equals `1`
   - Expected: caps_is_subset(["cap.device_gpu"], w.granted_of(weak)) is false
   - Expected: caps_is_subset(["cap.net_scoped"], w.granted_of(weak)) is false
   - Expected: caps_is_subset(req.caps, ["cap.fs_read"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a pod member cannot inherit another pod member's capabilities")
var w = ContainerWorld.new()
val weak = w.sys_create("weak", "/containers/weak", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val strong = w.sys_create("strong", "/containers/strong", [200u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read", "cap.net_scoped", "cap.device_gpu"], false)
val pod = w.create_pod(7000u64, 7001u64)
# Both join the SAME pod sharing net + ipc — the maximum sharing the
# manager offers. Caps must still not flow between them.
w.sys_pod_wire(weak, pod, 1u32 | 2u32)
w.sys_pod_wire(strong, pod, 1u32 | 2u32)
expect(w.granted_of(weak).len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(caps_is_subset(["cap.device_gpu"], w.granted_of(weak))).to_equal(false)
expect(caps_is_subset(["cap.net_scoped"], w.granted_of(weak))).to_equal(false)
val req: SpawnRequest = w.sys_start(weak)
expect(caps_is_subset(req.caps, ["cap.fs_read"])).to_equal(true)
```

</details>

### escape/namespace: one container cannot resolve another's world

#### a container cannot resolve a sibling container's path

- Verify: a container cannot resolve a sibling container's path
   - Expected: w.path_decision(a, "/containers/b/secret") equals `deny`
   - Expected: w.path_decision(b, "/containers/a/secret") equals `deny`
   - Expected: w.path_decision(a, "/containers") equals `deny`
   - Expected: w.path_decision(a, "/containers/a/secret") equals `allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a container cannot resolve a sibling container's path")
var w = ContainerWorld.new()
val a = w.sys_create("a", "/containers/a", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val b = w.sys_create("b", "/containers/b", [200u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
expect(w.path_decision(a, "/containers/b/secret")).to_equal("deny")
expect(w.path_decision(b, "/containers/a/secret")).to_equal("deny")
expect(w.path_decision(a, "/containers")).to_equal("deny")
expect(w.path_decision(a, "/containers/a/secret")).to_equal("allow")
```

</details>

#### a container cannot resolve a sibling container's pid or a host pid

- Verify: a container cannot resolve a sibling container's pid or a host pid
   - Expected: w.pid_decision(a, 200u64) equals `deny`
   - Expected: w.pid_decision(b, 100u64) equals `deny`
   - Expected: w.pid_decision(a, 1u64) equals `deny`
   - Expected: w.pid_decision(a, 0u64) equals `deny`
   - Expected: w.pid_decision(a, 100u64) equals `allow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a container cannot resolve a sibling container's pid or a host pid")
var w = ContainerWorld.new()
val a = w.sys_create("a", "/containers/a", [100u64, 101u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val b = w.sys_create("b", "/containers/b", [200u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
expect(w.pid_decision(a, 200u64)).to_equal("deny")
expect(w.pid_decision(b, 100u64)).to_equal("deny")
# pid 1 is the host init — the crown jewel of a pid-namespace escape.
expect(w.pid_decision(a, 1u64)).to_equal("deny")
expect(w.pid_decision(a, 0u64)).to_equal("deny")
expect(w.pid_decision(a, 100u64)).to_equal("allow")
```

</details>

#### sharing a pod net and ipc does NOT widen the filesystem or pid view

- Verify: sharing a pod net and ipc does NOT widen the filesystem or pid view
   - Expected: w.view_of(a).net_handle equals `7000u64`
   - Expected: w.view_of(b).net_handle equals `7000u64`
   - Expected: w.path_decision(a, "/containers/b/secret") equals `deny`
   - Expected: w.pid_decision(a, 200u64) equals `deny`
   - Expected: w.path_decision(b, "/containers/a/secret") equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: sharing a pod net and ipc does NOT widen the filesystem or pid view")
var w = ContainerWorld.new()
val a = w.sys_create("a", "/containers/a", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val b = w.sys_create("b", "/containers/b", [200u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val pod = w.create_pod(7000u64, 7001u64)
# NS_NET | NS_IPC | NS_MOUNT | NS_PID — ask for EVERYTHING, including
# the mount and pid bits the manager deliberately does not implement.
w.sys_pod_wire(a, pod, 1u32 | 2u32 | 4u32 | 8u32)
w.sys_pod_wire(b, pod, 1u32 | 2u32 | 4u32 | 8u32)
# net/ipc are genuinely shared (the feature works)...
expect(w.view_of(a).net_handle).to_equal(7000u64)
expect(w.view_of(b).net_handle).to_equal(7000u64)
# ...but mount and pid did NOT cross, despite the mask asking.
expect(w.path_decision(a, "/containers/b/secret")).to_equal("deny")
expect(w.pid_decision(a, 200u64)).to_equal("deny")
expect(w.path_decision(b, "/containers/a/secret")).to_equal("deny")
```

</details>

#### the rootless default view resolves absolutely nothing

- Verify: the rootless default view resolves absolutely nothing
   - Expected: container_view_path_decision(r, "/") equals `deny`
   - Expected: container_view_path_decision(r, "/etc/shadow") equals `deny`
   - Expected: container_view_path_decision(r, "") equals `deny`
   - Expected: container_view_path_decision(r, "anything") equals `deny`
   - Expected: container_view_pid_decision(r, 1u64) equals `deny`
   - Expected: container_view_pid_decision(r, 0u64) equals `deny`
   - Expected: container_view_pid_decision(r, 999999u64) equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: the rootless default view resolves absolutely nothing")
val r = container_view_rootless()
expect(container_view_path_decision(r, "/")).to_equal("deny")
expect(container_view_path_decision(r, "/etc/shadow")).to_equal("deny")
expect(container_view_path_decision(r, "")).to_equal("deny")
expect(container_view_path_decision(r, "anything")).to_equal("deny")
expect(container_view_pid_decision(r, 1u64)).to_equal("deny")
expect(container_view_pid_decision(r, 0u64)).to_equal("deny")
expect(container_view_pid_decision(r, 999999u64)).to_equal("deny")
```

</details>

#### a STOPPED container resolves nothing and holds no capability

- Verify: a STOPPED container resolves nothing and holds no capability
   - Expected: w.path_decision(c, "/containers/victim/app") equals `allow`
   - Expected: lc.state equals `stopped`
   - Expected: w.path_decision(c, "/containers/victim/app") equals `deny`
   - Expected: w.path_decision(c, "/containers/victim") equals `deny`
   - Expected: w.pid_decision(c, 100u64) equals `deny`
   - Expected: w.granted_of(c).len() equals `0`
   - Expected: w.view_of(c).net_handle equals `0u64`
   - Expected: w.view_of(c).ipc_handle equals `0u64`
   - Expected: w.svc_world_invariant() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a STOPPED container resolves nothing and holds no capability")
var w = ContainerWorld.new()
val c = w.sys_create("victim", "/containers/victim", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read", "cap.net_scoped"], false)
val req: SpawnRequest = w.sys_start(c)
expect(w.path_decision(c, "/containers/victim/app")).to_equal("allow")
val lc = w.sys_stop(c)
expect(lc.state).to_equal("stopped")
# every previously-allowed handle is now dead.
expect(w.path_decision(c, "/containers/victim/app")).to_equal("deny")
expect(w.path_decision(c, "/containers/victim")).to_equal("deny")
expect(w.pid_decision(c, 100u64)).to_equal("deny")
expect(w.granted_of(c).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(w.view_of(c).net_handle).to_equal(0u64)
expect(w.view_of(c).ipc_handle).to_equal(0u64)
expect(w.svc_world_invariant()).to_equal(true)
```

</details>

#### an EXITED container resolves nothing even after a pod wired it

- Verify: an EXITED container resolves nothing even after a pod wired it
   - Expected: w.view_of(c).net_handle equals `7000u64`
   - Expected: w.sys_monitor() equals `1`
   - Expected: w.path_decision(c, "/containers/victim/app") equals `deny`
   - Expected: w.pid_decision(c, 100u64) equals `deny`
   - Expected: w.granted_of(c).len() equals `0`
   - Expected: w.view_of(c).net_handle equals `0u64`
   - Expected: w.svc_world_invariant() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: an EXITED container resolves nothing even after a pod wired it")
var w = ContainerWorld.new()
val c = w.sys_create("victim", "/containers/victim", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val pod = w.create_pod(7000u64, 7001u64)
w.sys_pod_wire(c, pod, 1u32 | 2u32)
val req: SpawnRequest = w.sys_start(c)
expect(w.view_of(c).net_handle).to_equal(7000u64)
w.post_monitor_report(c, "exited", 0)
expect(w.sys_monitor()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(w.path_decision(c, "/containers/victim/app")).to_equal("deny")
expect(w.pid_decision(c, 100u64)).to_equal("deny")
expect(w.granted_of(c).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
# the shared pod endpoint was revoked too — no dangling net handle.
expect(w.view_of(c).net_handle).to_equal(0u64)
expect(w.svc_world_invariant()).to_equal(true)
```

</details>

### escape/leakage: the OCI edge never grants host net, devices, or hooks

#### every raw host-net capability token is stripped, ceiling or not

- Verify: every raw host-net capability token is stripped, ceiling or not
   - Expected: r.ok is true
   - Expected: r.spec.caps.len() equals `1`
   - Expected: r.spec.caps[0] equals `cap.fs_read`
   - Expected: spec_is_isolated_net(r.spec) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: every raw host-net capability token is stripped, ceiling or not")
# Ask under a ceiling that even LISTS the host-net tokens — the strip is
# unconditional, so a mis-written policy cannot re-open host networking.
val permissive = OciPolicy(
    allow_host_mounts: false,
    allow_devices: false,
    allow_hooks: false,
    max_unpack_count: 100000u64,
    max_unpack_size: 1073741824u64,
    require_digest: true,
    cap_ceiling: ["cap.fs_read", "cap.host_net", "cap.net_host", "cap.net_host_raw"]
)
val r = oci_import_checked(
    hostile_oci([], ["cap.fs_read", "cap.host_net", "cap.net_host", "cap.net_host_raw"], "/containers/evil", false),
    permissive
)
expect(r.ok).to_equal(true)
expect(r.spec.caps.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(r.spec.caps[0]).to_equal("cap.fs_read")
expect(spec_is_isolated_net(r.spec)).to_equal(true)
```

</details>

#### a device-node mount is rejected, including pseudo-device types

- Verify: a device-node mount is rejected, including pseudo-device types
   - Expected: r_dev.ok is false
   - Expected: r_devtmpfs.ok is false
   - Expected: r_devtmpfs.spec.root equals ``
   - Expected: r_mknod.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a device-node mount is rejected, including pseudo-device types")
# HOLE FOUND BY THIS SUITE (now fixed): the check exact-matched mtype
# "device", so "devtmpfs" carried /dev/mem straight through.
val p = locked_policy()
val r_dev = oci_import_checked(
    hostile_oci([OciMount(src: "/dev/sda", dest: "/dev/sda", mtype: "device")], ["cap.fs_read"], "/containers/evil", false), p)
expect(r_dev.ok).to_equal(false)
expect(r_dev.error).to_contain("device")

val r_devtmpfs = oci_import_checked(
    hostile_oci([OciMount(src: "/dev/mem", dest: "/dev/mem", mtype: "devtmpfs")], ["cap.fs_read"], "/containers/evil", false), p)
expect(r_devtmpfs.ok).to_equal(false)
expect(r_devtmpfs.spec.root).to_equal("")

val r_mknod = oci_import_checked(
    hostile_oci([OciMount(src: "devnode", dest: "/dev/kmsg", mtype: "mknod")], ["cap.fs_read"], "/containers/evil", false), p)
expect(r_mknod.ok).to_equal(false)
```

</details>

#### a raw host bind is rejected however the mount type is spelled

- Verify: a raw host bind is rejected however the mount type is spelled
   - Expected: r_bind.ok is false
   - Expected: r_rbind.ok is false
   - Expected: r_rbind.spec.caps.len() equals `0`
   - Expected: r_unknown.ok is false
   - Expected: r_tmpfs.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a raw host bind is rejected however the mount type is spelled")
# HOLE FOUND BY THIS SUITE (now fixed): only mtype == "bind" was
# checked, so "rbind" (and any unknown type) smuggled an absolute host
# source in. The rule now keys off the absolute host SOURCE, not the
# type name.
val p = locked_policy()
val r_bind = oci_import_checked(
    hostile_oci([OciMount(src: "/etc", dest: "/etc", mtype: "bind")], ["cap.fs_read"], "/containers/evil", false), p)
expect(r_bind.ok).to_equal(false)
expect(r_bind.error).to_contain("host bind mount denied")

val r_rbind = oci_import_checked(
    hostile_oci([OciMount(src: "/etc", dest: "/etc", mtype: "rbind")], ["cap.fs_read"], "/containers/evil", false), p)
expect(r_rbind.ok).to_equal(false)
expect(r_rbind.spec.caps.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement

val r_unknown = oci_import_checked(
    hostile_oci([OciMount(src: "/", dest: "/host", mtype: "overlay-future")], ["cap.fs_read"], "/containers/evil", false), p)
expect(r_unknown.ok).to_equal(false)

# ...and a genuine pseudo-fs mount (non-absolute source) still imports,
# so the rule is not "reject every mount".
val r_tmpfs = oci_import_checked(
    hostile_oci([OciMount(src: "tmpfs", dest: "/tmp", mtype: "tmpfs")], ["cap.fs_read"], "/containers/evil", false), p)
expect(r_tmpfs.ok).to_equal(true)
```

</details>

#### lifecycle hook injection is rejected outright

- Verify: lifecycle hook injection is rejected outright
   - Expected: r.ok is false
   - Expected: r.spec.caps.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: lifecycle hook injection is rejected outright")
val r = oci_import_checked(
    hostile_oci([], ["cap.fs_read"], "/containers/evil", true), locked_policy())
expect(r.ok).to_equal(false)
expect(r.error).to_contain("hooks")
expect(r.spec.caps.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### an unsigned image and an unpack bomb are both rejected

- Verify: an unsigned image and an unpack bomb are both rejected
   - Expected: r_unsigned.ok is false
   - Expected: r_bomb.ok is false
   - Expected: r_many.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: an unsigned image and an unpack bomb are both rejected")
val p = locked_policy()
var unsigned = hostile_oci([], ["cap.fs_read"], "/containers/evil", false)
unsigned.digest = ""
val r_unsigned = oci_import_checked(unsigned, p)
expect(r_unsigned.ok).to_equal(false)
expect(r_unsigned.error).to_contain("digest")

var bomb = hostile_oci([], ["cap.fs_read"], "/containers/evil", false)
bomb.unpack_size = 1099511627776u64
val r_bomb = oci_import_checked(bomb, p)
expect(r_bomb.ok).to_equal(false)
expect(r_bomb.error).to_contain("unpack")

var many = hostile_oci([], ["cap.fs_read"], "/containers/evil", false)
many.unpack_count = 100000000u64
val r_many = oci_import_checked(many, p)
expect(r_many.ok).to_equal(false)
expect(r_many.error).to_contain("unpack")
```

</details>

### escape/storage: COW layers are never shared or resurrected

#### two containers off the SAME base get DISTINCT writable layers

- Verify: two containers off the SAME base get DISTINCT writable layers
   - Expected: la == lb is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: two containers off the SAME base get DISTINCT writable layers")
# HOLE FOUND BY THIS SUITE (now fixed): the COW id was
# `digest + ":cow"`, so every container branched from one base was
# handed the SAME writable layer id — in a real COW backend that is
# container A reading and writing container B's files.
var w = ContainerWorld.new()
val a = w.sys_create("a", "/containers/a", [100u64], "sha256:shared", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val b = w.sys_create("b", "/containers/b", [200u64], "sha256:shared", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val la = w.snapshot_layer_of(a)
val lb = w.snapshot_layer_of(b)
expect(la == lb).to_equal(false)
# both still descend from the one content-addressed base.
expect(la).to_start_with("sha256:shared:cow")
expect(lb).to_start_with("sha256:shared:cow")
```

</details>

#### writes into one container's COW layer are invisible to its sibling

- Verify: writes into one container's COW layer are invisible to its sibling
   - Expected: w.snapshot_write_of(a, 1000u64) is true
   - Expected: w.snapshot_used_of(a) equals `1000u64`
   - Expected: w.snapshot_used_of(b) equals `0u64`
   - Expected: w.snapshot_write_of(b, 7u64) is true
   - Expected: w.snapshot_used_of(b) equals `7u64`
   - Expected: w.snapshot_used_of(a) equals `1000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: writes into one container's COW layer are invisible to its sibling")
var w = ContainerWorld.new()
val a = w.sys_create("a", "/containers/a", [100u64], "sha256:shared", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val b = w.sys_create("b", "/containers/b", [200u64], "sha256:shared", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
expect(w.snapshot_write_of(a, 1000u64)).to_equal(true)
expect(w.snapshot_used_of(a)).to_equal(1000u64)
# b's writable layer never moved — no shared-layer bleed.
expect(w.snapshot_used_of(b)).to_equal(0u64)
expect(w.snapshot_write_of(b, 7u64)).to_equal(true)
expect(w.snapshot_used_of(b)).to_equal(7u64)
expect(w.snapshot_used_of(a)).to_equal(1000u64)
```

</details>

#### a container cannot write past its own COW quota

- Verify: a container cannot write past its own COW quota
   - Expected: w.snapshot_write_of(a, 100u64) is true
   - Expected: w.snapshot_write_of(a, 1u64) is false
   - Expected: w.snapshot_used_of(a) equals `100u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a container cannot write past its own COW quota")
var w = ContainerWorld.new()
val a = w.sys_create("a", "/containers/a", [100u64], "sha256:shared", 1024u64, 100u64, 100u64, 64u64, ["cap.fs_read"], false)
expect(w.snapshot_write_of(a, 100u64)).to_equal(true)
# one byte over: refused, and NOTHING is written.
expect(w.snapshot_write_of(a, 1u64)).to_equal(false)
expect(w.snapshot_used_of(a)).to_equal(100u64)
```

</details>

#### a removed container's layers are unreachable and its refcount is gone

- Verify: a removed container's layers are unreachable and its refcount is gone
   - Expected: w.store_add_layer("sha256:dead", "", 512u64) is true
   - Expected: w.layer_refcount_of("sha256:dead") equals `1`
   - Expected: w.sys_monitor() equals `1`
   - Expected: w.was_reclaimed("sha256:dead") is true
   - Expected: w.store_has_layer("sha256:dead") is false
   - Expected: w.layer_refcount_of("sha256:dead") equals `0`
   - Expected: w.snapshot_live_of(a) is false
   - Expected: w.snapshot_layer_of(a) equals ``
   - Expected: w.live_snapshot_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a removed container's layers are unreachable and its refcount is gone")
var w = ContainerWorld.new()
val a = w.sys_create("a", "/containers/a", [100u64], "sha256:dead", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
expect(w.store_add_layer("sha256:dead", "", 512u64)).to_equal(true)
val req: SpawnRequest = w.sys_start(a)
expect(w.layer_refcount_of("sha256:dead")).to_equal(1)
# the container exits and is collected.
w.post_monitor_report(a, "exited", 0)
expect(w.sys_monitor()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val reclaimed = w.sys_gc()
expect(w.was_reclaimed("sha256:dead")).to_equal(true)
expect(w.store_has_layer("sha256:dead")).to_equal(false)
expect(w.layer_refcount_of("sha256:dead")).to_equal(0)
# the dead container's snapshot resolves to nothing — refcount abuse
# cannot walk back to a reclaimed layer.
expect(w.snapshot_live_of(a)).to_equal(false)
expect(w.snapshot_layer_of(a)).to_equal("")
expect(w.live_snapshot_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### GC never reclaims a layer a LIVE container still references

- Verify: GC never reclaims a layer a LIVE container still references
   - Expected: w.store_add_layer("sha256:keep", "", 512u64) is true
   - Expected: w.store_add_layer("sha256:drop", "", 512u64) is true
   - Expected: w.sys_monitor() equals `1`
   - Expected: w.was_reclaimed("sha256:drop") is true
   - Expected: w.was_reclaimed("sha256:keep") is false
   - Expected: w.store_has_layer("sha256:keep") is true
   - Expected: w.snapshot_live_of(live) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: GC never reclaims a layer a LIVE container still references")
var w = ContainerWorld.new()
val live = w.sys_create("live", "/containers/live", [100u64], "sha256:keep", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val dead = w.sys_create("dead", "/containers/dead", [200u64], "sha256:drop", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
expect(w.store_add_layer("sha256:keep", "", 512u64)).to_equal(true)
expect(w.store_add_layer("sha256:drop", "", 512u64)).to_equal(true)
val r1: SpawnRequest = w.sys_start(live)
val r2: SpawnRequest = w.sys_start(dead)
w.post_monitor_report(dead, "exited", 0)
expect(w.sys_monitor()).to_equal(1)  # oracle: 1 — named expected value from the requirement
val reclaimed = w.sys_gc()
# the dead container's base went; the live container's base survived.
expect(w.was_reclaimed("sha256:drop")).to_equal(true)
expect(w.was_reclaimed("sha256:keep")).to_equal(false)
expect(w.store_has_layer("sha256:keep")).to_equal(true)
expect(w.snapshot_live_of(live)).to_equal(true)
```

</details>

#### a manager restart tears down every brokered grant, live or not

- Verify: a manager restart tears down every brokered grant, live or not
   - Expected: w.svc_start(["vfs", "pm"]) is true
   - Expected: w.svc_holds_grants() is true
   - Expected: w.svc_restart() is true
   - Expected: w.svc_holds_grants() is false
   - Expected: w.granted_of(a).len() equals `0`
   - Expected: w.granted_of(b).len() equals `0`
   - Expected: w.path_decision(a, "/containers/a/app") equals `deny`
   - Expected: w.path_decision(b, "/containers/b/app") equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a manager restart tears down every brokered grant, live or not")
# A crashed manager must not leave containers holding the authority it
# vouched for and can no longer supervise.
var w = ContainerWorld.new()
val a = w.sys_create("a", "/containers/a", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val b = w.sys_create("b", "/containers/b", [200u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.net_scoped"], false)
val r1: SpawnRequest = w.sys_start(a)
val r2: SpawnRequest = w.sys_start(b)
expect(w.svc_start(["vfs", "pm"])).to_equal(true)
w.svc_acquire_grant("dev.block0")
w.svc_ready()
expect(w.svc_holds_grants()).to_equal(true)
expect(w.svc_restart()).to_equal(true)
# service-level: no inherited grant.
expect(w.svc_holds_grants()).to_equal(false)
# world-level: no container kept what the dead manager brokered.
expect(w.granted_of(a).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(w.granted_of(b).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(w.path_decision(a, "/containers/a/app")).to_equal("deny")
expect(w.path_decision(b, "/containers/b/app")).to_equal("deny")
```

</details>

### escape/calibration: the oracles do detect a real breach

#### CALIBRATION — a container seeded with a global root DOES escape

- Verify: CALIBRATION — a container seeded with a global root DOES escape
   - Expected: w.path_decision(breached, "/etc/shadow") equals `allow`
   - Expected: w.path_decision(breached, "/proc/1/root") equals `allow`
   - Expected: w.path_decision(sound, "/etc/shadow") equals `deny`
   - Expected: w.path_decision(breached, "/etc/../etc/shadow") equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: CALIBRATION — a container seeded with a global root DOES escape")
var w = ContainerWorld.new()
# seed_global_root: true is the defect injection — the container is
# handed "/" instead of its declared root.
val breached = w.sys_create("breached", "/containers/victim", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], true)
# Section 1's oracle is `path_decision(c, "/etc/shadow") == "deny"`.
# Against the breached build the SAME call observes "allow" — so that
# oracle is load-bearing, not vacuous.
expect(w.path_decision(breached, "/etc/shadow")).to_equal("allow")
expect(w.path_decision(breached, "/proc/1/root")).to_equal("allow")
# Contrast with the same call on a correctly-built container.
val sound = w.sys_create("sound", "/containers/victim", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
expect(w.path_decision(sound, "/etc/shadow")).to_equal("deny")
# The breach is NOT total — ".." is still refused even with a global
# root, which is why the traversal oracle needs its own calibration.
expect(w.path_decision(breached, "/etc/../etc/shadow")).to_equal("deny")
```

</details>

#### CALIBRATION — with the traversal check off, the escape mount IMPORTS

- Verify: CALIBRATION — with the traversal check off, the escape mount IMPORTS
   - Expected: oci_import_checked(attack, p).ok is false
   - Expected: breached.ok is true
   - Expected: breached.error equals ``
   - Expected: breached.spec.root equals `/containers/evil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: CALIBRATION — with the traversal check off, the escape mount IMPORTS")
val p = locked_policy()
val attack = hostile_oci([OciMount(src: "tmpfs", dest: "/tmp/../../etc", mtype: "tmpfs")], ["cap.fs_read"], "/containers/evil", false)
# Production path (check_traversal: true) rejects — section 1 proves it.
expect(oci_import_checked(attack, p).ok).to_equal(false)
# Defect-injected path: the same hostile config sails through, so
# section 1's `r.ok == false` oracle would be RED.
val breached = oci_import_checked_ex(attack, p, false)
expect(breached.ok).to_equal(true)
expect(breached.error).to_equal("")
# ...and the escaping destination reached the imported container.
expect(breached.spec.root).to_equal("/containers/evil")
```

</details>

#### CALIBRATION — a stale global-root view WOULD be reported by the detector

- Verify: CALIBRATION — a stale global-root view WOULD be reported by the detector
   - Expected: container_view_allows_path(stale, "/etc/shadow") is true
   - Expected: container_view_allows_pid(stale, 100u64) is true
   - Expected: w.svc_world_invariant() is true
   - Expected: w.path_decision(c, "/etc/shadow") equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: CALIBRATION — a stale global-root view WOULD be reported by the detector")
# svc_world_invariant is the section-21 detector several attacks above
# assert `true` on. Show the primitive it consults reports a breach, so
# the detector is not a constant-true.
var w = ContainerWorld.new()
val c = w.sys_create("breached", "/containers/victim", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], true)
val req: SpawnRequest = w.sys_start(c)
# A dead container that KEPT a global root: the oracle says "allow".
val stale = container_view_create("/", [100u64])
expect(container_view_allows_path(stale, "/etc/shadow")).to_equal(true)
expect(container_view_allows_pid(stale, 100u64)).to_equal(true)
# The real teardown does the opposite — the property under test.
val lc = w.sys_stop(c)
expect(w.svc_world_invariant()).to_equal(true)
expect(w.path_decision(c, "/etc/shadow")).to_equal("deny")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** `doc/04_architecture/os/container/podman_mdsoc_container_arch.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-SERVICES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `92c13c217474fa7aacdc55c7c6effe26cb7aa1a4d216e52482d4f6c83f78bb50`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `92c13c217474fa7aacdc55c7c6effe26cb7aa1a4d216e52482d4f6c83f78bb50`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `92c13c217474fa7aacdc55c7c6effe26cb7aa1a4d216e52482d4f6c83f78bb50`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/services/container/container_escape_suite_spec.spl
mirror: doc/06_spec/01_unit/os/services/container/container_escape_suite_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/services/container/container_escape_suite_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/container/container_escape_suite_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/container/container_escape_suite_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/container/container_escape_suite_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/services/container/container_escape_suite_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a .. component in a resolved path is denied, never normalized away' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/container/container_escape_suite_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an absolute host path outside the root is denied' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/container/container_escape_suite_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a sibling path that merely CONTAINS the root as a prefix is denied' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
