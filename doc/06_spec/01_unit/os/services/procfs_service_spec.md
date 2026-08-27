# @manual: primary

> Purpose: Prove that ProcfsService initial state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that ProcfsService initial state.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #G7 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/os/services/procfs_service_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that ProcfsService initial state.
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

### ProcfsService initial state

#### constructs with zero registered nodes

- Verify: constructs with zero registered nodes
   - Expected: svc.procfs_node_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: constructs with zero registered nodes")
"""Verify the node count starts at 0 on a fresh service."""
val svc = ProcfsService.new()
expect(svc.procfs_node_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### PROC_FILE constant equals 0

- Verify: PROC_FILE constant equals 0
   - Expected: PROC_FILE equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: PROC_FILE constant equals 0")
"""File node kind constant must be 0."""
expect(PROC_FILE).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### PROC_DIR constant equals 1

- Verify: PROC_DIR constant equals 1
   - Expected: PROC_DIR equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: PROC_DIR constant equals 1")
"""Directory node kind constant must be 1."""
expect(PROC_DIR).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### procfs_list_pids_path returns /proc

- Verify: procfs_list_pids_path returns /proc
   - Expected: svc.procfs_list_pids_path() equals `/proc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: procfs_list_pids_path returns /proc")
"""The canonical procfs root path must be '/proc'."""
val svc = ProcfsService.new()
expect(svc.procfs_list_pids_path()).to_equal("/proc")
```

</details>

### ProcfsService procfs_mount

#### mount stores pm_endpoint on service

- Verify: mount stores pm_endpoint on service
   - Expected: svc.pm_endpoint equals `7777`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: mount stores pm_endpoint on service")
"""After procfs_mount the service pm_endpoint must equal the argument."""
var svc = ProcfsService.new()
svc.procfs_mount(7777)
expect(svc.pm_endpoint).to_equal(7777)  # oracle: 7777 — named expected value from the requirement
```

</details>

#### mount does not create any ECS nodes

- Verify: mount does not create any ECS nodes
   - Expected: svc.procfs_node_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: mount does not create any ECS nodes")
"""procfs_mount must not register any entities (count stays 0)."""
var svc = ProcfsService.new()
svc.procfs_mount(8888)
expect(svc.procfs_node_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### ProcfsService procfs_node_register

#### register increments node count

- Verify: register increments node count
   - Expected: svc.procfs_node_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: register increments node count")
"""After registering one node the count must be 1."""
var svc = ProcfsService.new()
val _e = svc.procfs_node_register("/proc/1", 1, PROC_DIR)
expect(svc.procfs_node_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### register returns the first live entity (id 0, generation 1)

- Verify: register returns the first live entity (id 0, generation 1)
   - Expected: e.id equals `0`
   - Expected: e.generation equals `1`
   - Expected: e.is_null() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: register returns the first live entity (id 0, generation 1)")
"""procfs_node_register must return a live entity; the first slot is id 0.

(The old `id > 0` expectation was wrong: EntityAllocator hands out id 0
first. It only "passed" while two-hop mutation loss hid allocator state.)
"""
var svc = ProcfsService.new()
val e = svc.procfs_node_register("/proc/1/status", 1, PROC_FILE)
expect(e.id).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(e.generation).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(e.is_null()).to_equal(false)
```

</details>

### ProcfsService procfs_node_lookup

#### lookup registered node returns its source pid

- Verify: lookup registered node returns its source pid
   - Expected: pid equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: lookup registered node returns its source pid")
"""procfs_node_lookup must return the pid used at registration."""
var svc = ProcfsService.new()
val _e = svc.procfs_node_register("/proc/42/cmdline", 42, PROC_FILE)
val pid = svc.procfs_node_lookup("/proc/42/cmdline")
expect(pid).to_equal(42)  # oracle: 42 — named expected value from the requirement
```

</details>

#### lookup missing path returns -2

- Verify: lookup missing path returns -2
   - Expected: pid equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: lookup missing path returns -2")
"""procfs_node_lookup must return -ENOENT (-2) for unknown paths."""
val svc = ProcfsService.new()
val pid = svc.procfs_node_lookup("/proc/9999/status")
expect(pid).to_equal(-2)  # oracle: -2 — named expected value from the requirement
```

</details>

#### lookup different path does not match registered node

- Verify: lookup different path does not match registered node
   - Expected: pid equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: lookup different path does not match registered node")
"""Lookup of a different path than registered must return -ENOENT."""
var svc = ProcfsService.new()
val _e = svc.procfs_node_register("/proc/1/maps", 1, PROC_FILE)
val pid = svc.procfs_node_lookup("/proc/1/status")
expect(pid).to_equal(-2)  # oracle: -2 — named expected value from the requirement
```

</details>

### ProcfsService cross-entity identity (two-hop mutation-loss regression)

#### three node registrations get distinct entity ids 0, 1, 2

- Verify: three node registrations get distinct entity ids 0, 1, 2
   - Expected: e0.id equals `0`
   - Expected: e1.id equals `1`
   - Expected: e2.id equals `2`
   - Expected: e0.generation equals `1`
   - Expected: e1.generation equals `1`
   - Expected: e2.generation equals `1`
   - Expected: svc.procfs_node_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: three node registrations get distinct entity ids 0, 1, 2")
var svc = ProcfsService.new()
val e0 = svc.procfs_node_register("/proc/1/status",  1, PROC_FILE)
val e1 = svc.procfs_node_register("/proc/42/status", 42, PROC_FILE)
val e2 = svc.procfs_node_register("/proc/7",         7, PROC_DIR)
expect(e0.id).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(e1.id).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(e2.id).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(e0.generation).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(e1.generation).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(e2.generation).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(svc.procfs_node_count()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### per-node pid components stay isolated across three nodes

- Verify: per-node pid components stay isolated across three nodes
   - Expected: svc.procfs_node_lookup("/proc/1/status") equals `1`
   - Expected: svc.procfs_node_lookup("/proc/42/status") equals `42`
   - Expected: svc.procfs_node_lookup("/proc/7") equals `7`
   - Expected: svc.procfs_node_lookup("/proc/999") equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: per-node pid components stay isolated across three nodes")
var svc = ProcfsService.new()
val _e0 = svc.procfs_node_register("/proc/1/status",  1, PROC_FILE)
val _e1 = svc.procfs_node_register("/proc/42/status", 42, PROC_FILE)
val _e2 = svc.procfs_node_register("/proc/7",         7, PROC_DIR)
expect(svc.procfs_node_lookup("/proc/1/status")).to_equal(1)
expect(svc.procfs_node_lookup("/proc/42/status")).to_equal(42)
expect(svc.procfs_node_lookup("/proc/7")).to_equal(7)
expect(svc.procfs_node_lookup("/proc/999")).to_equal(-2)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-SERVICES-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2556f53cdd4d215c9ead1a6eab324453c654499a233127d8f4b467f41905f41b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2556f53cdd4d215c9ead1a6eab324453c654499a233127d8f4b467f41905f41b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2556f53cdd4d215c9ead1a6eab324453c654499a233127d8f4b467f41905f41b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/services/procfs_service_spec.spl
mirror: doc/06_spec/01_unit/os/services/procfs_service_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/services/procfs_service_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/procfs_service_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/procfs_service_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/procfs_service_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/services/procfs_service_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs with zero registered nodes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/procfs_service_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PROC_FILE constant equals 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/procfs_service_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PROC_DIR constant equals 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
