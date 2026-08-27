# @manual: primary

> Purpose: Prove that DevfsService initial state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that DevfsService initial state.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #G7 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/os/services/devfs_service_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that DevfsService initial state.
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

### DevfsService initial state

#### constructs with zero registered devices

- Verify: constructs with zero registered devices
   - Expected: svc.dev_list_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: constructs with zero registered devices")
"""Verify the node count starts at 0 on a fresh service."""
val svc = DevfsService.new()
expect(svc.dev_list_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### DEV_CHAR constant equals 0

- Verify: DEV_CHAR constant equals 0
   - Expected: DEV_CHAR equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: DEV_CHAR constant equals 0")
"""Character device kind constant must be 0."""
expect(DEV_CHAR).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### DEV_BLOCK constant equals 1

- Verify: DEV_BLOCK constant equals 1
   - Expected: DEV_BLOCK equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: DEV_BLOCK constant equals 1")
"""Block device kind constant must be 1."""
expect(DEV_BLOCK).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### DevfsService dev_register

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
"""dev_register must return a live entity; the first allocated slot is id 0.

(The old `id > 0` expectation was wrong: EntityAllocator hands out id 0
first. It only "passed" while two-hop mutation loss hid allocator state.)
"""
var svc = DevfsService.new()
val e = svc.dev_register("tty0", 0, DEV_CHAR, 0o620, 100)
expect(e.id).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(e.generation).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(e.is_null()).to_equal(false)
```

</details>

#### register increments device count

- Verify: register increments device count
   - Expected: svc.dev_list_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: register increments device count")
"""After one registration the count must be 1."""
var svc = DevfsService.new()
val _e = svc.dev_register("sda", 1, DEV_BLOCK, 0o660, 200)
expect(svc.dev_list_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### register two devices yields count 2

- Verify: register two devices yields count 2
   - Expected: svc.dev_list_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: register two devices yields count 2")
"""After two registrations the count must be 2."""
var svc = DevfsService.new()
val _a = svc.dev_register("tty0", 0, DEV_CHAR, 0o620, 100)
val _b = svc.dev_register("sda",  1, DEV_BLOCK, 0o660, 200)
expect(svc.dev_list_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### DevfsService dev_lookup

#### lookup registered device returns its backend endpoint

- Verify: lookup registered device returns its backend endpoint
   - Expected: ep equals `9999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: lookup registered device returns its backend endpoint")
"""dev_lookup must return the exact endpoint value used at registration."""
var svc = DevfsService.new()
val _e = svc.dev_register("null", 3, DEV_CHAR, 0o666, 9999)
val ep = svc.dev_lookup("null")
expect(ep).to_equal(9999)  # oracle: 9999 — named expected value from the requirement
```

</details>

#### lookup missing device returns -2

- Verify: lookup missing device returns -2
   - Expected: ep equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: lookup missing device returns -2")
"""dev_lookup must return -ENOENT (-2) when name is not registered."""
val svc = DevfsService.new()
val ep = svc.dev_lookup("nonexistent")
expect(ep).to_equal(-2)  # oracle: -2 — named expected value from the requirement
```

</details>

### DevfsService dev_unregister

#### unregister decrements count

- Verify: unregister decrements count
   - Expected: svc.dev_list_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: unregister decrements count")
"""After registering then unregistering one device the count is 0."""
var svc = DevfsService.new()
val _e = svc.dev_register("tty1", 4, DEV_CHAR, 0o620, 300)
svc.dev_unregister("tty1")
expect(svc.dev_list_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### unregister makes lookup return -2

- Verify: unregister makes lookup return -2
   - Expected: ep equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: unregister makes lookup return -2")
"""Lookup of an unregistered device must return -ENOENT."""
var svc = DevfsService.new()
val _e = svc.dev_register("tty2", 5, DEV_CHAR, 0o620, 400)
svc.dev_unregister("tty2")
val ep = svc.dev_lookup("tty2")
expect(ep).to_equal(-2)  # oracle: -2 — named expected value from the requirement
```

</details>

### DevfsService dev_permissions_of

#### permissions_of returns registered mode

- Verify: permissions_of returns registered mode
   - Expected: mode equals `0o640`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: permissions_of returns registered mode")
"""dev_permissions_of must return the exact mode bits from registration."""
var svc = DevfsService.new()
val _e = svc.dev_register("mem", 1, DEV_CHAR, 0o640, 500)
val mode = svc.dev_permissions_of("mem")
expect(mode).to_equal(0o640)
```

</details>

#### permissions_of unknown device returns 0

- Verify: permissions_of unknown device returns 0
   - Expected: mode equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: permissions_of unknown device returns 0")
"""dev_permissions_of must return 0 for an unregistered name."""
val svc = DevfsService.new()
val mode = svc.dev_permissions_of("nosuchdev")
expect(mode).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### DevfsService cross-entity identity (two-hop mutation-loss regression)

#### three registrations in one world get distinct entity ids 0, 1, 2

- Verify: three registrations in one world get distinct entity ids 0, 1, 2
   - Expected: e0.id equals `0`
   - Expected: e1.id equals `1`
   - Expected: e2.id equals `2`
   - Expected: e0.generation equals `1`
   - Expected: e1.generation equals `1`
   - Expected: e2.generation equals `1`
   - Expected: svc.dev_list_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: three registrations in one world get distinct entity ids 0, 1, 2")
var svc = DevfsService.new()
val e0 = svc.dev_register("tty0",  0, DEV_CHAR,  0o620, 100)
val e1 = svc.dev_register("sda",   1, DEV_BLOCK, 0o660, 200)
val e2 = svc.dev_register("null",  2, DEV_CHAR,  0o666, 300)
expect(e0.id).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(e1.id).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(e2.id).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(e0.generation).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(e1.generation).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(e2.generation).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(svc.dev_list_count()).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### per-entity components stay isolated across three devices

- Verify: per-entity components stay isolated across three devices
   - Expected: svc.dev_lookup("tty0") equals `100`
   - Expected: svc.dev_lookup("sda") equals `200`
   - Expected: svc.dev_lookup("null") equals `300`
   - Expected: svc.dev_permissions_of("tty0") equals `0o620`
   - Expected: svc.dev_permissions_of("sda") equals `0o660`
   - Expected: svc.dev_permissions_of("null") equals `0o666`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: per-entity components stay isolated across three devices")
var svc = DevfsService.new()
val _e0 = svc.dev_register("tty0",  0, DEV_CHAR,  0o620, 100)
val _e1 = svc.dev_register("sda",   1, DEV_BLOCK, 0o660, 200)
val _e2 = svc.dev_register("null",  2, DEV_CHAR,  0o666, 300)
expect(svc.dev_lookup("tty0")).to_equal(100)
expect(svc.dev_lookup("sda")).to_equal(200)
expect(svc.dev_lookup("null")).to_equal(300)
expect(svc.dev_permissions_of("tty0")).to_equal(0o620)
expect(svc.dev_permissions_of("sda")).to_equal(0o660)
expect(svc.dev_permissions_of("null")).to_equal(0o666)
```

</details>

#### unregistering the middle device leaves the two siblings intact

- Verify: unregistering the middle device leaves the two siblings intact
   - Expected: svc.dev_list_count() equals `2`
   - Expected: svc.dev_lookup("sda") equals `-2`
   - Expected: svc.dev_lookup("tty0") equals `100`
   - Expected: svc.dev_lookup("null") equals `300`
   - Expected: svc.dev_permissions_of("tty0") equals `0o620`
   - Expected: svc.dev_permissions_of("null") equals `0o666`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: unregistering the middle device leaves the two siblings intact")
var svc = DevfsService.new()
val _e0 = svc.dev_register("tty0",  0, DEV_CHAR,  0o620, 100)
val _e1 = svc.dev_register("sda",   1, DEV_BLOCK, 0o660, 200)
val _e2 = svc.dev_register("null",  2, DEV_CHAR,  0o666, 300)
svc.dev_unregister("sda")
expect(svc.dev_list_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(svc.dev_lookup("sda")).to_equal(-2)
expect(svc.dev_lookup("tty0")).to_equal(100)
expect(svc.dev_lookup("null")).to_equal(300)
expect(svc.dev_permissions_of("tty0")).to_equal(0o620)
expect(svc.dev_permissions_of("null")).to_equal(0o666)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `d7ac4b0f1b7b3129f592454b7b12b0327c1c3cd07db3ec5b181c648bf31c82e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d7ac4b0f1b7b3129f592454b7b12b0327c1c3cd07db3ec5b181c648bf31c82e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d7ac4b0f1b7b3129f592454b7b12b0327c1c3cd07db3ec5b181c648bf31c82e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/services/devfs_service_spec.spl
mirror: doc/06_spec/01_unit/os/services/devfs_service_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/services/devfs_service_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/devfs_service_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/devfs_service_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/devfs_service_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/services/devfs_service_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs with zero registered devices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/devfs_service_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DEV_CHAR constant equals 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/devfs_service_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DEV_BLOCK constant equals 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
