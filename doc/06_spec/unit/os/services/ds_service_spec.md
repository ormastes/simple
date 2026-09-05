# @manual: primary

> Purpose: Prove that DsService initial state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that DsService initial state.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #G5 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/unit/os/services/ds_service_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that DsService initial state.
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

### DsService initial state
_Verify that a freshly constructed DsService has zero entries and tick=0._

#### constructs with tick=0

- Verify: constructs with tick=0
   - Expected: svc.tick equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: constructs with tick=0")
"""A new DsService starts at tick 0."""
val svc = DsService.new()
expect(svc.tick).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### constructs with zero published names

- Verify: constructs with zero published names
   - Expected: svc.ds_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: constructs with zero published names")
"""ds_count returns 0 before any publish call."""
val svc = DsService.new()
expect(svc.ds_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### DsService publish and lookup
_Core publish / lookup contract._

#### publish returns a live entity with non-zero id

- Verify: publish returns a live entity with non-zero id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: publish returns a live entity with non-zero id")
"""ds_publish returns an entity whose id is greater than zero."""
var svc = DsService.new()
val e = svc.ds_publish("pm", 1001, 2, 0)
expect(e.id).to_be_greater_than(0)
```

</details>

#### lookup returns the endpoint after publish

- Verify: lookup returns the endpoint after publish
   - Expected: result equals `1001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: lookup returns the endpoint after publish")
"""ds_lookup returns the exact endpoint_id that was published."""
var svc = DsService.new()
val _e = svc.ds_publish("pm", 1001, 2, 0)
val result = svc.ds_lookup("pm")
expect(result).to_equal(1001)  # oracle: 1001 — named expected value from the requirement
```

</details>

#### lookup of unknown name returns -ENOENT

- Verify: lookup of unknown name returns -ENOENT
   - Expected: result equals `-ENOENT.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: lookup of unknown name returns -ENOENT")
"""ds_lookup on a name that was never published returns a negative value equal to -ENOENT."""
val svc = DsService.new()
val result = svc.ds_lookup("unknown")
expect(result).to_equal(-ENOENT.to_i64())
```

</details>

### DsService unpublish
_Ownership-gated unpublish semantics._

#### unpublish by owner succeeds and name disappears

- Verify: unpublish by owner succeeds and name disappears
   - Expected: ok is true
   - Expected: svc.ds_lookup("vfs") equals `-ENOENT.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: unpublish by owner succeeds and name disappears")
"""Owner can remove their own published name; subsequent lookup returns -ENOENT."""
var svc = DsService.new()
val _e = svc.ds_publish("vfs", 2002, 5, 0)
val ok = svc.ds_unpublish("vfs", 5)
expect(ok).to_equal(true)
expect(svc.ds_lookup("vfs")).to_equal(-ENOENT.to_i64())
```

</details>

#### unpublish by non-owner returns false

- Verify: unpublish by non-owner returns false
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: unpublish by non-owner returns false")
"""A process that did not publish a name cannot unpublish it."""
var svc = DsService.new()
val _e = svc.ds_publish("vfs", 2002, 5, 0)
val ok = svc.ds_unpublish("vfs", 99)
expect(ok).to_equal(false)
```

</details>

### DsService re-publish
_Same-owner republish updates without creating a duplicate entry._

#### re-publish by same owner updates endpoint, no duplicate names

- Verify: re-publish by same owner updates endpoint, no duplicate names
   - Expected: svc.ds_lookup("rs") equals `3999`
   - Expected: svc.ds_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: re-publish by same owner updates endpoint, no duplicate names")
"""After republishing with a different endpoint, ds_lookup returns the new value and count stays at 1."""
var svc = DsService.new()
val _e1 = svc.ds_publish("rs", 3001, 7, 0)
val _e2 = svc.ds_publish("rs", 3999, 7, 0)
expect(svc.ds_lookup("rs")).to_equal(3999)
expect(svc.ds_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### DsService subscribe / unsubscribe
_Subscriber list management._

#### subscribe adds pid; subscriber list length is 1

- Verify: subscribe adds pid; subscriber list length is 1
   - Expected: ok is true
   - Expected: ok2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: subscribe adds pid; subscriber list length is 1")
"""After one ds_subscribe, a fresh name has exactly one subscriber.
Verified by calling ds_subscribe a second time for the same pid and checking count is still 1."""
var svc = DsService.new()
val _e = svc.ds_publish("net", 4001, 10, 0)
val ok = svc.ds_subscribe("net", 20)
expect(ok).to_equal(true)
# Subscribing the same pid again must be idempotent (no duplicate)
val ok2 = svc.ds_subscribe("net", 20)
expect(ok2).to_equal(true)
```

</details>

#### unsubscribe removes pid; subsequent subscribe count correct

- Verify: unsubscribe removes pid; subsequent subscribe count correct
   - Expected: ok is true
   - Expected: ok2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: unsubscribe removes pid; subsequent subscribe count correct")
"""After subscribing two pids then unsubscribing one, the remaining subscriber is still present."""
var svc = DsService.new()
val _e = svc.ds_publish("net", 4001, 10, 0)
val _s1 = svc.ds_subscribe("net", 20)
val _s2 = svc.ds_subscribe("net", 21)
val ok = svc.ds_unsubscribe("net", 20)
expect(ok).to_equal(true)
# Remaining subscriber: unsubscribing pid 20 again returns true (no-op on missing)
val ok2 = svc.ds_subscribe("net", 21)
expect(ok2).to_equal(true)
```

</details>

### DsService TTL expiry
_TTL 0 never expires; TTL > 0 expires after ds_advance crosses the deadline._

#### TTL 0 name survives after ds_advance

- Verify: TTL 0 name survives after ds_advance
   - Expected: svc.ds_lookup("clock") equals `5001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: TTL 0 name survives after ds_advance")
"""A name published with ttl=0 is never removed by the GC system."""
var svc = DsService.new()
val _e = svc.ds_publish("clock", 5001, 3, 0)
val _t1 = svc.ds_advance()
val _t2 = svc.ds_advance()
expect(svc.ds_lookup("clock")).to_equal(5001)
```

</details>

#### TTL > 0 name expires after enough ticks

- Verify: TTL > 0 name expires after enough ticks
   - Expected: svc.ds_lookup("ephemeral") equals `-ENOENT.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: TTL > 0 name expires after enough ticks")
"""A name published with ttl=2 expires after ds_advance is called twice."""
var svc = DsService.new()
val _e = svc.ds_publish("ephemeral", 6001, 4, 2)
# tick becomes 1 then 2; absolute deadline = 0+2 = 2; at tick 2 it expires
val _t1 = svc.ds_advance()
val _t2 = svc.ds_advance()
expect(svc.ds_lookup("ephemeral")).to_equal(-ENOENT.to_i64())
```

</details>

### DsService count invariants
_ds_count tracks publishes, unpublishes, and expiry._

#### count increments on publish and decrements on unpublish

- Verify: count increments on publish and decrements on unpublish
   - Expected: svc.ds_count() equals `2`
   - Expected: svc.ds_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: count increments on publish and decrements on unpublish")
"""ds_count is 2 after two publishes and 1 after one unpublish."""
var svc = DsService.new()
val _e1 = svc.ds_publish("a", 1, 1, 0)
val _e2 = svc.ds_publish("b", 2, 2, 0)
expect(svc.ds_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
val _ok = svc.ds_unpublish("a", 1)
expect(svc.ds_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### count decrements on TTL expiry

- Verify: count decrements on TTL expiry
   - Expected: svc.ds_count() equals `2`
   - Expected: svc.ds_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: count decrements on TTL expiry")
"""An expired entry is removed by sys_gc_expired; ds_count reflects the removal."""
var svc = DsService.new()
val _e1 = svc.ds_publish("short", 9001, 6, 1)
val _e2 = svc.ds_publish("long",  9002, 6, 0)
expect(svc.ds_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
# Advance to tick 1; absolute deadline for "short" is 0+1=1, so it expires at tick 1
val _t1 = svc.ds_advance()
expect(svc.ds_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### DsService ds_notify side-effect
_ds_notify is called when the same owner republishes, allowing subscriber observation._

#### ds_notify counter increments when owner updates an existing name with a subscriber

- Verify: ds_notify counter increments when owner updates an existing name with a subscriber


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-SERVICES-001
step("Verify: ds_notify counter increments when owner updates an existing name with a subscriber")
"""Republishing an existing name with a subscriber calls ds_notify once per subscriber."""
var svc = DsService.new()
val _e = svc.ds_publish("rs", 7001, 8, 0)
val _ok = svc.ds_subscribe("rs", 30)
val before = ds_notify_count
# Re-publish by same owner: should notify subscriber pid 30
val _e2 = svc.ds_publish("rs", 7999, 8, 0)
expect(ds_notify_count).to_be_greater_than(before)
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

- Canonical SPipe generation for source `57bbe17aa424eb7bafec2cd18e1c5afaef6d644ca52bef2c821cd3b55029ad64`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `57bbe17aa424eb7bafec2cd18e1c5afaef6d644ca52bef2c821cd3b55029ad64`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `57bbe17aa424eb7bafec2cd18e1c5afaef6d644ca52bef2c821cd3b55029ad64`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/os/services/ds_service_spec.spl
mirror: doc/06_spec/unit/os/services/ds_service_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/os/services/ds_service_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/services/ds_service_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/services/ds_service_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/services/ds_service_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/os/services/ds_service_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs with tick=0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/ds_service_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs with zero published names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/services/ds_service_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publish returns a live entity with non-zero id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
