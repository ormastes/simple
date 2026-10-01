# @manual: primary

> Purpose: Prove that container-manager: sys_monitor records the observed exit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that container-manager: sys_monitor records the observed exit.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-CTR-MDSOC |
| Category | Runtime / OS / Container |
| Status | In Progress |
| Design | doc/04_architecture/os/container/podman_mdsoc_container_arch.md |
| Source | `test/01_unit/os/services/container/container_monitor_gc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that container-manager: sys_monitor records the observed exit.
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

### container-manager: sys_monitor records the observed exit

#### a monitored container that exits records exited with the exact code

- Verify: a monitored container that exits records exited with the exact code
   - Expected: w.lifecycle_state(c1) equals `running`
   - Expected: w.report_pending(c1) is true
   - Expected: reaped equals `1`
   - Expected: w.lifecycle_state(c1) equals `exited`
   - Expected: w.lifecycle_exit(c1) equals `42`
   - Expected: w.monitor_state(c1) equals `reaped`
   - Expected: w.report_pending(c1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a monitored container that exits records exited with the exact code")
var w = ContainerWorld.new()
val c1 = w.sys_create("app1", "/c1", [100u64], "sha256:aaa", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val req: SpawnRequest = w.sys_start(c1)
expect(w.lifecycle_state(c1)).to_equal("running")
# the monitor capsule observes the workload leaving with code 42.
w.post_monitor_report(c1, "exited", 42)
expect(w.report_pending(c1)).to_equal(true)
val reaped = w.sys_monitor()
expect(reaped).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(w.lifecycle_state(c1)).to_equal("exited")
expect(w.lifecycle_exit(c1)).to_equal(42)  # oracle: 42 — named expected value from the requirement
# reaped: the per-container monitor is done, its handle released.
expect(w.monitor_state(c1)).to_equal("reaped")
expect(w.report_pending(c1)).to_equal(false)
```

</details>

#### a still-running report only moves the monitor state, never the lifecycle

- Verify: a still-running report only moves the monitor state, never the lifecycle
   - Expected: w.sys_monitor() equals `0`
   - Expected: w.lifecycle_state(c1) equals `running`
   - Expected: w.lifecycle_exit(c1) equals `-1`
   - Expected: w.monitor_state(c1) equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a still-running report only moves the monitor state, never the lifecycle")
var w = ContainerWorld.new()
val c1 = w.sys_create("app1", "/c1", [100u64], "sha256:aaa", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
val req: SpawnRequest = w.sys_start(c1)
w.post_monitor_report(c1, "running", -1)
expect(w.sys_monitor()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(w.lifecycle_state(c1)).to_equal("running")
expect(w.lifecycle_exit(c1)).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect(w.monitor_state(c1)).to_equal("running")
```

</details>

### container-manager: crash restart re-acquires, never inherits (§21)

#### a crashed container is restart-eligible yet holds NO stale grant

- Verify: a crashed container is restart-eligible yet holds NO stale grant
   - Expected: w.allows_path(c1, "/c1/app") is true
   - Expected: w.sys_monitor() equals `1`
   - Expected: w.lifecycle_exit(c1) equals `137`
   - Expected: w.restart_eligible(c1) is true
   - Expected: w.granted_of(c1).len() equals `0`
   - Expected: w.allows_path(c1, "/c1/app") is false
   - Expected: w.allows_pid(c1, 100u64) is false
   - Expected: w.path_decision(c1, "/c1/app") equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a crashed container is restart-eligible yet holds NO stale grant")
var w = ContainerWorld.new()
val c1 = w.sys_create("app1", "/c1", [100u64, 101u64], "sha256:aaa", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read", "cap.net_scoped"], false)
w.set_restart_policy(c1, "on-failure", 3)
val req: SpawnRequest = w.sys_start(c1)
expect(w.allows_path(c1, "/c1/app")).to_equal(true)
# the monitor observes a crash (SIGKILL-shaped code).
w.post_monitor_report(c1, "crashed", 137)
expect(w.sys_monitor()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(w.lifecycle_exit(c1)).to_equal(137)  # oracle: 137 — named expected value from the requirement
# eligible for the restart policy ...
expect(w.restart_eligible(c1)).to_equal(true)
# ... but every grant is GONE: no pouch, no path, no pid.
expect(w.granted_of(c1).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(w.allows_path(c1, "/c1/app")).to_equal(false)
expect(w.allows_pid(c1, 100u64)).to_equal(false)
expect(w.path_decision(c1, "/c1/app")).to_equal("deny")
```

</details>

#### sys_restart runs on freshly re-acquired authority

- Verify: sys_restart runs on freshly re-acquired authority
   - Expected: w.sys_monitor() equals `1`
   - Expected: w.granted_of(c1).len() equals `0`
   - Expected: w.lifecycle_state(c1) equals `running`
   - Expected: w.monitor_state(c1) equals `running`
   - Expected: w.granted_of(c1).len() equals `1`
   - Expected: w.granted_of(c1)[0] equals `cap.fs_read`
   - Expected: again.caps.len() equals `1`
   - Expected: again.budget equals `2048u64`
   - Expected: w.allows_path(c1, "/c1/app") is true
   - Expected: w.restart_retries(c1) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: sys_restart runs on freshly re-acquired authority")
var w = ContainerWorld.new()
val c1 = w.sys_create("app1", "/c1", [100u64], "sha256:aaa", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read", "cap.net_scoped"], false)
w.set_restart_policy(c1, "always", 2)
val req: SpawnRequest = w.sys_start(c1)
w.post_monitor_report(c1, "exited", 3)
expect(w.sys_monitor()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(w.granted_of(c1).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
# restart supplies the authority again — narrower than before.
val again: SpawnRequest = w.sys_restart(c1, ["cap.fs_read"], "/c1", [100u64], 512u64, 2048u64, 50u64, 32u64)
expect(w.lifecycle_state(c1)).to_equal("running")
expect(w.monitor_state(c1)).to_equal("running")
expect(w.granted_of(c1).len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(w.granted_of(c1)[0]).to_equal("cap.fs_read")
# the request carries exactly the re-acquired set, not the dead one.
expect(again.caps.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(again.budget).to_equal(2048u64)
expect(w.allows_path(c1, "/c1/app")).to_equal(true)
expect(w.restart_retries(c1)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### a clean exit under on-failure is NOT restart-eligible

- Verify: a clean exit under on-failure is NOT restart-eligible
   - Expected: w.sys_monitor() equals `1`
   - Expected: w.lifecycle_exit(c1) equals `0`
   - Expected: w.restart_eligible(c1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a clean exit under on-failure is NOT restart-eligible")
var w = ContainerWorld.new()
val c1 = w.sys_create("app1", "/c1", [100u64], "sha256:aaa", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
w.set_restart_policy(c1, "on-failure", 3)
val req: SpawnRequest = w.sys_start(c1)
w.post_monitor_report(c1, "exited", 0)
expect(w.sys_monitor()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(w.lifecycle_exit(c1)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(w.restart_eligible(c1)).to_equal(false)
```

</details>

### container-manager: ref-tracked GC (§6.4)

#### gc reclaims an unreferenced layer but NOT one a live container uses

- Verify: gc reclaims an unreferenced layer but NOT one a live container uses
   - Expected: w.layer_refcount_of("sha256:base") equals `1`
   - Expected: w.layer_refcount_of("sha256:orphan") equals `0`
   - Expected: reclaimed.len() equals `1`
   - Expected: reclaimed[0] equals `sha256:orphan`
   - Expected: w.store_has_layer("sha256:base") is true
   - Expected: w.store_has_layer("sha256:orphan") is false
   - Expected: w.store_layer_count() equals `1`
   - Expected: w.was_reclaimed("sha256:orphan") is true
   - Expected: w.was_reclaimed("sha256:base") is false
   - Expected: w.snapshot_live_of(c1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: gc reclaims an unreferenced layer but NOT one a live container uses")
var w = ContainerWorld.new()
w.store_add_layer("sha256:base", "", 100u64)
w.store_add_layer("sha256:orphan", "", 50u64)
# a live container branches a COW snapshot off sha256:base.
val c1 = w.sys_create("app1", "/c1", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
expect(w.layer_refcount_of("sha256:base")).to_equal(1)
expect(w.layer_refcount_of("sha256:orphan")).to_equal(0)
val reclaimed = w.sys_gc()
# exactly one digest reclaimed, and it is the orphan BY VALUE.
expect(reclaimed.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(reclaimed[0]).to_equal("sha256:orphan")
# the live container's base survives, by value.
expect(w.store_has_layer("sha256:base")).to_equal(true)
expect(w.store_has_layer("sha256:orphan")).to_equal(false)
expect(w.store_layer_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(w.was_reclaimed("sha256:orphan")).to_equal(true)
expect(w.was_reclaimed("sha256:base")).to_equal(false)
# and its snapshot is untouched — the container is still alive.
expect(w.snapshot_live_of(c1)).to_equal(true)
```

</details>

#### a layer deeper in a live parent chain is never reclaimed

- Verify: a layer deeper in a live parent chain is never reclaimed
   - Expected: w.layer_refcount_of("sha256:b0") equals `2`
   - Expected: w.layer_refcount_of("sha256:b1") equals `1`
   - Expected: reclaimed.len() equals `0`
   - Expected: w.store_layer_count() equals `2`
   - Expected: w.store_has_layer("sha256:b0") is true
   - Expected: w.store_has_layer("sha256:b1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a layer deeper in a live parent chain is never reclaimed")
var w = ContainerWorld.new()
w.store_add_layer("sha256:b0", "", 100u64)
w.store_add_layer("sha256:b1", "sha256:b0", 20u64)
val c1 = w.sys_create("app1", "/c1", [100u64], "sha256:b1", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
# b0 is referenced twice: by b1's parent link and by the live chain.
expect(w.layer_refcount_of("sha256:b0")).to_equal(2)
expect(w.layer_refcount_of("sha256:b1")).to_equal(1)
val reclaimed = w.sys_gc()
expect(reclaimed.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(w.store_layer_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(w.store_has_layer("sha256:b0")).to_equal(true)
expect(w.store_has_layer("sha256:b1")).to_equal(true)
```

</details>

### container-manager: sys_gc keeps explicit persistent volumes

#### a persistent volume survives while the COW snapshot is reclaimed

- Verify: a persistent volume survives while the COW snapshot is reclaimed
   - Expected: w.live_volume_count() equals `2`
   - Expected: w.snapshot_live_of(c1) is true
   - Expected: w.layer_refcount_of("sha256:v") equals `1`
   - Expected: life.state equals `stopped`
   - Expected: w.snapshot_live_of(c1) is false
   - Expected: w.live_snapshot_count() equals `0`
   - Expected: reclaimed.len() equals `1`
   - Expected: reclaimed[0] equals `sha256:v`
   - Expected: w.store_layer_count() equals `0`
   - Expected: w.volume_live("data") is true
   - Expected: w.volume_live("scratch") is false
   - Expected: w.live_volume_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a persistent volume survives while the COW snapshot is reclaimed")
var w = ContainerWorld.new()
w.store_add_layer("sha256:v", "", 100u64)
val c1 = w.sys_create("app1", "/c1", [100u64], "sha256:v", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
w.attach_volume(c1, "data", "/data", true)
w.attach_volume(c1, "scratch", "/scratch", false)
val req: SpawnRequest = w.sys_start(c1)
expect(w.live_volume_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(w.snapshot_live_of(c1)).to_equal(true)
expect(w.layer_refcount_of("sha256:v")).to_equal(1)
# stop then collect.
val life = w.sys_stop(c1)
expect(life.state).to_equal("stopped")
val reclaimed = w.sys_gc()
# COW snapshot released and its RO base reclaimed (nothing else holds it).
expect(w.snapshot_live_of(c1)).to_equal(false)
expect(w.live_snapshot_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(reclaimed.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(reclaimed[0]).to_equal("sha256:v")
expect(w.store_layer_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
# the EXPLICIT persistent volume survives container removal; the
# anonymous one does not.
expect(w.volume_live("data")).to_equal(true)
expect(w.volume_live("scratch")).to_equal(false)
expect(w.live_volume_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### container-manager: atomic snapshot rollback (§6.4)

#### rollback returns exactly the base digest and zeroes the writable layer

- Verify: rollback returns exactly the base digest and zeroes the writable layer
   - Expected: w.snapshot_write_of(c1, 1024u64) is true
   - Expected: w.snapshot_used_of(c1) equals `1024u64`
   - Expected: base equals `sha256:base`
   - Expected: w.snapshot_used_of(c1) equals `0u64`
   - Expected: w.snapshot_layer_of(c1) equals `sha256:base:cow:rb`
   - Expected: w.snapshot_live_of(c1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: rollback returns exactly the base digest and zeroes the writable layer")
var w = ContainerWorld.new()
w.store_add_layer("sha256:base", "", 100u64)
val c1 = w.sys_create("app1", "/c1", [100u64], "sha256:base", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
expect(w.snapshot_write_of(c1, 1024u64)).to_equal(true)
expect(w.snapshot_used_of(c1)).to_equal(1024u64)
val base = w.snapshot_rollback_of(c1)
expect(base).to_equal("sha256:base")
expect(w.snapshot_used_of(c1)).to_equal(0u64)
expect(w.snapshot_layer_of(c1)).to_equal("sha256:base:cow:rb")
expect(w.snapshot_live_of(c1)).to_equal(true)
```

</details>

#### rollback with a missing RO base changes NOTHING

- Verify: rollback with a missing RO base changes NOTHING
   - Expected: w.snapshot_write_of(c1, 10u64) is true
   - Expected: base equals ``
   - Expected: w.snapshot_used_of(c1) equals `10u64`
   - Expected: w.snapshot_layer_of(c1) equals `sha256:ghost:cow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: rollback with a missing RO base changes NOTHING")
var w = ContainerWorld.new()
# note: no store_add_layer — the base digest is not in the store.
val c1 = w.sys_create("app1", "/c1", [100u64], "sha256:ghost", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
expect(w.snapshot_write_of(c1, 10u64)).to_equal(true)
val base = w.snapshot_rollback_of(c1)
expect(base).to_equal("")
# unchanged: same bytes, same writable layer id.
expect(w.snapshot_used_of(c1)).to_equal(10u64)
expect(w.snapshot_layer_of(c1)).to_equal("sha256:ghost:cow")
```

</details>

#### a write past the per-container quota is refused and writes nothing

- Verify: a write past the per-container quota is refused and writes nothing
   - Expected: w.snapshot_write_of(c1, 5000u64) is false
   - Expected: w.snapshot_used_of(c1) equals `0u64`
   - Expected: w.snapshot_write_of(c1, 4096u64) is true
   - Expected: w.snapshot_used_of(c1) equals `4096u64`
   - Expected: w.snapshot_write_of(c1, 1u64) is false
   - Expected: w.snapshot_used_of(c1) equals `4096u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: a write past the per-container quota is refused and writes nothing")
var w = ContainerWorld.new()
val c1 = w.sys_create("app1", "/c1", [100u64], "sha256:q", 1024u64, 4096u64, 100u64, 64u64, ["cap.fs_read"], false)
expect(w.snapshot_write_of(c1, 5000u64)).to_equal(false)
expect(w.snapshot_used_of(c1)).to_equal(0u64)
expect(w.snapshot_write_of(c1, 4096u64)).to_equal(true)
expect(w.snapshot_used_of(c1)).to_equal(4096u64)
expect(w.snapshot_write_of(c1, 1u64)).to_equal(false)
expect(w.snapshot_used_of(c1)).to_equal(4096u64)
```

</details>

### container-storage: the §6.4 free-function API

#### layer_refcount, snapshot_rollback and gc_collect agree on one store

- Verify: layer_refcount, snapshot_rollback and gc_collect agree on one store
   - Expected: layer_refcount(s, "sha256:a") equals `1`
   - Expected: rb.ok is true
   - Expected: rb.base_digest equals `sha256:a`
   - Expected: s2.release_snapshot(1u64) is true
   - Expected: layer_refcount(s2, "sha256:a") equals `0`
   - Expected: g.reclaimed.len() equals `1`
   - Expected: g.reclaimed[0] equals `sha256:a`
   - Expected: g.store.layer_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: layer_refcount, snapshot_rollback and gc_collect agree on one store")
var s = LayerStore.new()
s.add_layer("sha256:a", "", 10u64)
s.add_snapshot("cow-a", "sha256:a", 1u64, 100u64)
expect(layer_refcount(s, "sha256:a")).to_equal(1)
val rb = snapshot_rollback(s, 1u64)
expect(rb.ok).to_equal(true)
expect(rb.base_digest).to_equal("sha256:a")
# release the only reference, then collect.
var s2 = rb.store
expect(s2.release_snapshot(1u64)).to_equal(true)
expect(layer_refcount(s2, "sha256:a")).to_equal(0)
val g = gc_collect(s2)
expect(g.reclaimed.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(g.reclaimed[0]).to_equal("sha256:a")
expect(g.store.layer_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### rollback of an unknown container is a no-op

- Verify: rollback of an unknown container is a no-op
   - Expected: rb.ok is false
   - Expected: rb.base_digest equals ``
   - Expected: rb.store.layer_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: rollback of an unknown container is a no-op")
var s = LayerStore.new()
s.add_layer("sha256:a", "", 10u64)
val rb = snapshot_rollback(s, 999u64)
expect(rb.ok).to_equal(false)
expect(rb.base_digest).to_equal("")
expect(rb.store.layer_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `40e10405d9643dbcf2e289a3235fb48b10a144e1d1abff9476151f471593db02`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `40e10405d9643dbcf2e289a3235fb48b10a144e1d1abff9476151f471593db02`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `40e10405d9643dbcf2e289a3235fb48b10a144e1d1abff9476151f471593db02`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/services/container/container_monitor_gc_spec.spl
mirror: doc/06_spec/01_unit/os/services/container/container_monitor_gc_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/services/container/container_monitor_gc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/container/container_monitor_gc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/container/container_monitor_gc_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/container/container_monitor_gc_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/services/container/container_monitor_gc_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a monitored container that exits records exited with the exact code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/container/container_monitor_gc_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a still-running report only moves the monitor state, never the lifecycle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/container/container_monitor_gc_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a crashed container is restart-eligible yet holds NO stale grant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
