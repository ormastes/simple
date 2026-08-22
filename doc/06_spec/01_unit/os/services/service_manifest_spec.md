# service_v1 Typed Service Manifest Contract

> Verifies the service manifest behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# service_v1 Typed Service Manifest Contract

Verifies the service manifest behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/01_unit/os/services/service_manifest_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the service manifest behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### service_v1 readiness gating

#### denies start while a readiness dependency is not ready

- Verify: denies start while a readiness dependency is not ready
   - Expected: can_start(m, ["clock"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-001
# @req: REQ-SVC-
step("Verify: denies start while a readiness dependency is not ready")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var m = ServiceManifest.create("netd", "1.0")
m.readiness_deps = ["clock", "vfs"]
# only clock is up
expect(can_start(m, ["clock"])).to_equal(false)
```

</details>

#### allows start once every readiness dependency is ready

- Verify: allows start once every readiness dependency is ready
   - Expected: can_start(m, ["clock", "vfs", "pcimgr"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-001
# @req: REQ-SVC-
step("Verify: allows start once every readiness dependency is ready")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var m = ServiceManifest.create("netd", "1.0")
m.readiness_deps = ["clock", "vfs"]
expect(can_start(m, ["clock", "vfs", "pcimgr"])).to_equal(true)
```

</details>

#### allows start immediately when there are no dependencies

- Verify: allows start immediately when there are no dependencies
   - Expected: can_start(m, []) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-001
# @req: REQ-SVC-
step("Verify: allows start immediately when there are no dependencies")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var m = ServiceManifest.create("clock", "1.0")
expect(can_start(m, [])).to_equal(true)
```

</details>

### service_v1 health degradation

#### progresses Ready -> Degraded -> Failed on repeated bad health

- Verify: progresses Ready -> Degraded -> Failed on repeated bad health
   - Expected: m.state equals `Ready`
   - Expected: degraded.state equals `Degraded`
   - Expected: failed.state equals `Failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-001
# @req: REQ-SVC-
step("Verify: progresses Ready -> Degraded -> Failed on repeated bad health")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: a good health check returns the service to Ready
   - Expected: degraded.state equals `Degraded`
   - Expected: recovered.state equals `Ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-001
# @req: REQ-SVC-
step("Verify: a good health check returns the service to Ready")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: denies restart once restart_count reaches max_restarts
   - Expected: should_restart("on_failure", 0, 3) is true
   - Expected: should_restart("on_failure", 2, 3) is true
   - Expected: should_restart("on_failure", 3, 3) is false
   - Expected: should_restart("on_failure", 4, 3) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-001
# @req: REQ-SVC-
step("Verify: denies restart once restart_count reaches max_restarts")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# policy on_failure, max 3
expect(should_restart("on_failure", 0, 3)).to_equal(true)
expect(should_restart("on_failure", 2, 3)).to_equal(true)
expect(should_restart("on_failure", 3, 3)).to_equal(false)
expect(should_restart("on_failure", 4, 3)).to_equal(false)
```

</details>

#### never-policy services are never restarted

- Verify: never-policy services are never restarted
   - Expected: should_restart("never", 0, 5) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-001
# @req: REQ-SVC-
step("Verify: never-policy services are never restarted")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect(should_restart("never", 0, 5)).to_equal(false)
```

</details>

### service_v1 watchdog

#### drives a stalled Ready service to Failed past the watchdog deadline

- Verify: drives a stalled Ready service to Failed past the watchdog deadline
   - Expected: tripped.state equals `Failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-001
# @req: REQ-SVC-
step("Verify: drives a stalled Ready service to Failed past the watchdog deadline")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: leaves a heartbeating Ready service untouched before the deadline
   - Expected: ok.state equals `Ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-001
# @req: REQ-SVC-
step("Verify: leaves a heartbeating Ready service untouched before the deadline")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: clears ALL device and secret grants on restart (absolute oracle)
   - Expected: holds_grants(m) is true
   - Expected: m.granted_handles.len() equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: restarted.granted_handles.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: holds_grants(restarted) is false
   - Expected: restarted.state equals `Restarting`
   - Expected: restarted.restart_count equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-001
# @req: REQ-SVC-
step("Verify: clears ALL device and secret grants on restart (absolute oracle)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var m = ServiceManifest.create("nvme-user", "1.0")
# pre-crash the service held live device + secret grants
m.granted_handles = ["bar-tok-30", "irq-tok-31", "secret-key-9"]
m = mark_ready(mark_starting(m))
expect(holds_grants(m)).to_equal(true)
expect(m.granted_handles.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

val restarted = on_restart(m)
# THE invariant: a restarted service retains NO stale grants
expect(restarted.granted_handles.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(holds_grants(restarted)).to_equal(false)
expect(restarted.state).to_equal("Restarting")
expect(restarted.restart_count).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### does not mutate the pre-crash manifest when producing the restart copy

- Verify: does not mutate the pre-crash manifest when producing the restart copy
   - Expected: m.granted_handles.len() equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: restarted.granted_handles.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-001
# @req: REQ-SVC-
step("Verify: does not mutate the pre-crash manifest when producing the restart copy")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var m = ServiceManifest.create("nvme-user", "1.0")
m.granted_handles = ["bar-tok-30"]
val restarted = on_restart(m)
# original still holds its grant (value-type copy semantics)
expect(m.granted_handles.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(restarted.granted_handles.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `386c25ab70f5e6aa04c8b3aba619f6e2bd4d6b6b0a75b87446341d0598ab868f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `386c25ab70f5e6aa04c8b3aba619f6e2bd4d6b6b0a75b87446341d0598ab868f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `386c25ab70f5e6aa04c8b3aba619f6e2bd4d6b6b0a75b87446341d0598ab868f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/services/service_manifest_spec.spl
mirror: doc/06_spec/01_unit/os/services/service_manifest_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/service_manifest_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/services/service_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/service_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
