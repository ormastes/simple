# service_v1 Typed Service Manifest Contract

> Absolute-oracle spec for the pure lifecycle/health/watchdog/restart state

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# service_v1 Typed Service Manifest Contract

Absolute-oracle spec for the pure lifecycle/health/watchdog/restart state

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/01_unit/os/services/service_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Master plan:** doc/01_research/domain/simpleos_production_host_master_plan.md §4, §20, §21

Absolute-oracle spec for the pure lifecycle/health/watchdog/restart state
machine in src/os/services/service_manifest.spl. The load-bearing scenario is
the §21 invariant: on_restart() must yield a manifest holding zero device or
secret grants, even when the pre-crash manifest held several.

## Scenarios

### service_v1 readiness gating

#### denies start while a readiness dependency is not ready

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- denies start while a readiness dependency is not ready
   - Expected: can_start(m, ["clock"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("denies start while a readiness dependency is not ready")
var m = ServiceManifest.create("netd", "1.0")
m.readiness_deps = ["clock", "vfs"]
# only clock is up
expect(can_start(m, ["clock"])).to_equal(false)
```

</details>

#### allows start once every readiness dependency is ready

- allows start once every readiness dependency is ready
   - Expected: can_start(m, ["clock", "vfs", "pcimgr"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("allows start once every readiness dependency is ready")
var m = ServiceManifest.create("netd", "1.0")
m.readiness_deps = ["clock", "vfs"]
expect(can_start(m, ["clock", "vfs", "pcimgr"])).to_equal(true)
```

</details>

#### allows start immediately when there are no dependencies

- allows start immediately when there are no dependencies
   - Expected: can_start(m, []) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("allows start immediately when there are no dependencies")
var m = ServiceManifest.create("clock", "1.0")
expect(can_start(m, [])).to_equal(true)
```

</details>

### service_v1 health degradation

#### progresses Ready -> Degraded -> Failed on repeated bad health

- progresses Ready -> Degraded -> Failed on repeated bad health
   - Expected: m.state equals `Ready`
   - Expected: degraded.state equals `Degraded`
   - Expected: failed.state equals `Failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("progresses Ready -> Degraded -> Failed on repeated bad health")
var m = ServiceManifest.create("gpud", "2.1")
m = mark_starting(m)
m = mark_ready(m)
expect(m.state).to_equal("Ready")
val degraded = record_health(m, false)
expect(degraded.state).to_equal("Degraded")
val failed = record_health(degraded, false)
expect(failed.state).to_equal("Failed")
```

</details>

#### a good health check returns the service to Ready

- a good health check returns the service to Ready
   - Expected: degraded.state equals `Degraded`
   - Expected: recovered.state equals `Ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a good health check returns the service to Ready")
var m = ServiceManifest.create("gpud", "2.1")
m = mark_ready(mark_starting(m))
val degraded = record_health(m, false)
expect(degraded.state).to_equal("Degraded")
val recovered = record_health(degraded, true)
expect(recovered.state).to_equal("Ready")
```

</details>

### service_v1 restart-storm bound

#### denies restart once restart_count reaches max_restarts

- denies restart once restart_count reaches max_restarts
   - Expected: should_restart("on_failure", 0, 3) is true
   - Expected: should_restart("on_failure", 2, 3) is true
   - Expected: should_restart("on_failure", 3, 3) is false
   - Expected: should_restart("on_failure", 4, 3) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("denies restart once restart_count reaches max_restarts")
# policy on_failure, max 3
expect(should_restart("on_failure", 0, 3)).to_equal(true)
expect(should_restart("on_failure", 2, 3)).to_equal(true)
expect(should_restart("on_failure", 3, 3)).to_equal(false)
expect(should_restart("on_failure", 4, 3)).to_equal(false)
```

</details>

#### never-policy services are never restarted

- never-policy services are never restarted
   - Expected: should_restart("never", 0, 5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("never-policy services are never restarted")
expect(should_restart("never", 0, 5)).to_equal(false)
```

</details>

### service_v1 watchdog

#### drives a stalled Ready service to Failed past the watchdog deadline

- drives a stalled Ready service to Failed past the watchdog deadline
   - Expected: tripped.state equals `Failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("drives a stalled Ready service to Failed past the watchdog deadline")
var m = ServiceManifest.create("watchdogd", "1.0")
m.watchdog_timeout_ms = 5000
m = mark_ready(mark_starting(m))
m = record_heartbeat(m, 1000)
# 1000 + 5000 = 6000 deadline; now = 6001 is past it
val tripped = check_watchdog(m, 6001)
expect(tripped.state).to_equal("Failed")
```

</details>

#### leaves a heartbeating Ready service untouched before the deadline

- leaves a heartbeating Ready service untouched before the deadline
   - Expected: ok.state equals `Ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("leaves a heartbeating Ready service untouched before the deadline")
var m = ServiceManifest.create("watchdogd", "1.0")
m.watchdog_timeout_ms = 5000
m = mark_ready(mark_starting(m))
m = record_heartbeat(m, 1000)
val ok = check_watchdog(m, 5500)
expect(ok.state).to_equal("Ready")
```

</details>

### service_v1 §21 restart-no-stale-grant invariant

#### clears ALL device and secret grants on restart (absolute oracle)

- clears ALL device and secret grants on restart (absolute oracle)
   - Expected: holds_grants(m) is true
   - Expected: m.granted_handles.len() equals `3`
   - Expected: restarted.granted_handles.len() equals `0`
   - Expected: holds_grants(restarted) is false
   - Expected: restarted.state equals `Restarting`
   - Expected: restarted.restart_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clears ALL device and secret grants on restart (absolute oracle)")
var m = ServiceManifest.create("nvme-user", "1.0")
# pre-crash the service held live device + secret grants
m.granted_handles = ["bar-tok-30", "irq-tok-31", "secret-key-9"]
m = mark_ready(mark_starting(m))
expect(holds_grants(m)).to_equal(true)
expect(m.granted_handles.len()).to_equal(3)

val restarted = on_restart(m)
# THE invariant: a restarted service retains NO stale grants
expect(restarted.granted_handles.len()).to_equal(0)
expect(holds_grants(restarted)).to_equal(false)
expect(restarted.state).to_equal("Restarting")
expect(restarted.restart_count).to_equal(1)
```

</details>

#### does not mutate the pre-crash manifest when producing the restart copy

- does not mutate the pre-crash manifest when producing the restart copy
   - Expected: m.granted_handles.len() equals `1`
   - Expected: restarted.granted_handles.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not mutate the pre-crash manifest when producing the restart copy")
var m = ServiceManifest.create("nvme-user", "1.0")
m.granted_handles = ["bar-tok-30"]
val restarted = on_restart(m)
# original still holds its grant (value-type copy semantics)
expect(m.granted_handles.len()).to_equal(1)
expect(restarted.granted_handles.len()).to_equal(0)
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

- `REQ-SSPEC-UNIT`
- `REQ-SVC-service_v1-001`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f4bded2c81a7f4953be77825be7e32f4b012352de3f8df81d10745d12695d7ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f4bded2c81a7f4953be77825be7e32f4b012352de3f8df81d10745d12695d7ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f4bded2c81a7f4953be77825be7e32f4b012352de3f8df81d10745d12695d7ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/services/service_manifest_spec.spl
mirror: doc/06_spec/01_unit/os/services/service_manifest_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/services/service_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/service_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/service_manifest_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/service_manifest_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/services/service_manifest_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies start while a readiness dependency is not ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/service_manifest_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows start once every readiness dependency is ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/service_manifest_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows start immediately when there are no dependencies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
