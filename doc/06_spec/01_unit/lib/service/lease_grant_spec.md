# Lease Grant Specification

> As a service daemon operator, I need the shared lease manager in

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lease Grant Specification

As a service daemon operator, I need the shared lease manager in

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/service/lease_grant_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a service daemon operator, I need the shared lease manager in
`src/lib/nogc_sync_mut/service/lease_manager.spl` to serialize mutations:
exactly one exclusive holder at a time, many shared holders, a BUSY message
naming the blocker, and release restoring availability.

This spec exercises the REAL product module. It previously declared its own
private copy of `LeaseManager` and therefore proved nothing about `src/`.

## Scenarios

### Lease Grant - Exclusive Semantics

#### grants exclusive lease when no leases are held

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- grants exclusive lease when no leases are held
   - Expected: result.ok is true
   - Expected: active_lease_count(mgr) equals `1i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grants exclusive lease when no leases are held")
var mgr = lease_manager_new()
val pid = rt_getpid()
val result = try_acquire_exclusive(mgr, pid, 30000i64)
expect(result.ok).to_equal(true)
val lid = result.lease_id
expect(lid.len()).to_be_greater_than(0i64)
expect(active_lease_count(mgr)).to_equal(1i64)
```

</details>

#### rejects second exclusive lease while first is held

- rejects second exclusive lease while first is held
   - Expected: first.ok is true
   - Expected: second.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects second exclusive lease while first is held")
var mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
expect(first.ok).to_equal(true)
expect(second.ok).to_equal(false)
val msg = second.busy_message
expect(msg).to_contain("BUSY")
val fid = first.lease_id
expect(msg).to_contain(fid)
```

</details>

#### grants exclusive after release

- grants exclusive after release
   - Expected: released is true
   - Expected: active_lease_count(mgr) equals `0i64`
   - Expected: second.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grants exclusive after release")
var mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
val released = release_lease(mgr, first.lease_id)
expect(released).to_equal(true)
expect(active_lease_count(mgr)).to_equal(0i64)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
expect(second.ok).to_equal(true)
```

</details>

#### generates unique lease IDs

- generates unique lease IDs
   - Expected: same is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates unique lease IDs")
var mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
release_lease(mgr, first.lease_id)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
val fid = first.lease_id
val sid = second.lease_id
val same = fid == sid
expect(same).to_equal(false)
```

</details>

#### reports an active exclusive lease

- reports an active exclusive lease
   - Expected: first.ok is true
   - Expected: has_active_exclusive(mgr) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an active exclusive lease")
var mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 30000i64)
expect(first.ok).to_equal(true)
expect(has_active_exclusive(mgr)).to_equal(true)
```

</details>

### Lease Grant - Shared Semantics

#### grants shared lease when no leases are held

- grants shared lease when no leases are held
   - Expected: result.ok is true
   - Expected: has_active_exclusive(mgr) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grants shared lease when no leases are held")
var mgr = lease_manager_new()
val pid = rt_getpid()
val result = try_acquire_shared(mgr, pid, 5000i64)
expect(result.ok).to_equal(true)
expect(has_active_exclusive(mgr)).to_equal(false)
```

</details>

#### grants multiple shared leases concurrently

- grants multiple shared leases concurrently
   - Expected: first.ok is true
   - Expected: second.ok is true
   - Expected: active_lease_count(mgr) equals `2i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grants multiple shared leases concurrently")
var mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_shared(mgr, pid, 5000i64)
val second = try_acquire_shared(mgr, pid, 5000i64)
expect(first.ok).to_equal(true)
expect(second.ok).to_equal(true)
expect(active_lease_count(mgr)).to_equal(2i64)
```

</details>

#### rejects shared lease while exclusive is held

- rejects shared lease while exclusive is held
   - Expected: excl.ok is true
   - Expected: shared_result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects shared lease while exclusive is held")
var mgr = lease_manager_new()
val pid = rt_getpid()
val excl = try_acquire_exclusive(mgr, pid, 30000i64)
val shared_result = try_acquire_shared(mgr, pid, 5000i64)
expect(excl.ok).to_equal(true)
expect(shared_result.ok).to_equal(false)
val msg = shared_result.busy_message
expect(msg).to_contain("BUSY")
```

</details>

#### rejects exclusive while shared is held

- rejects exclusive while shared is held
   - Expected: shared_result.ok is true
   - Expected: excl.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects exclusive while shared is held")
var mgr = lease_manager_new()
val pid = rt_getpid()
val shared_result = try_acquire_shared(mgr, pid, 5000i64)
val excl = try_acquire_exclusive(mgr, pid, 30000i64)
expect(shared_result.ok).to_equal(true)
expect(excl.ok).to_equal(false)
```

</details>

#### grants exclusive after all shared released

- grants exclusive after all shared released
   - Expected: active_lease_count(mgr) equals `0i64`
   - Expected: excl.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grants exclusive after all shared released")
var mgr = lease_manager_new()
val pid = rt_getpid()
val s1 = try_acquire_shared(mgr, pid, 5000i64)
val s2 = try_acquire_shared(mgr, pid, 5000i64)
release_lease(mgr, s1.lease_id)
release_lease(mgr, s2.lease_id)
expect(active_lease_count(mgr)).to_equal(0i64)
val excl = try_acquire_exclusive(mgr, pid, 30000i64)
expect(excl.ok).to_equal(true)
```

</details>

#### BUSY message names the blocking holder pid

- BUSY message names the blocking holder pid


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BUSY message names the blocking holder pid")
var mgr = lease_manager_new()
val pid = rt_getpid()
val excl = try_acquire_exclusive(mgr, pid, 30000i64)
val shared_result = try_acquire_shared(mgr, pid, 5000i64)
val msg = shared_result.busy_message
expect(msg).to_contain("BUSY")
expect(msg).to_contain("exclusive")
```

</details>

### Lease Grant - Ghost Reclaim

#### reclaims a lease whose TTL has elapsed

- reclaims a lease whose TTL has elapsed
   - Expected: first.ok is true
   - Expected: active_lease_count(mgr) equals `0i64`
   - Expected: second.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reclaims a lease whose TTL has elapsed")
var mgr = lease_manager_new()
val pid = rt_getpid()
val first = try_acquire_exclusive(mgr, pid, 0i64)
expect(first.ok).to_equal(true)
expect(active_lease_count(mgr)).to_equal(0i64)
val second = try_acquire_exclusive(mgr, pid, 30000i64)
expect(second.ok).to_equal(true)
```

</details>

#### reclaims a lease whose holder pid is dead

- reclaims a lease whose holder pid is dead
   - Expected: first.ok is true
   - Expected: active_lease_count(mgr) equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reclaims a lease whose holder pid is dead")
var mgr = lease_manager_new()
val dead_pid = 999999i64
val first = try_acquire_exclusive(mgr, dead_pid, 30000i64)
expect(first.ok).to_equal(true)
expect(active_lease_count(mgr)).to_equal(0i64)
```

</details>

### Lease Grant - Lease ID Monotonicity (regression: every id was lease-1)

#### issues three DISTINCT ids across acquire/release cycles

- issues three DISTINCT ids across acquire/release cycles
   - Expected: a_id == b_id is false
   - Expected: b_id == c_id is false
   - Expected: a_id == c_id is false
   - Expected: a_id == a_id is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("issues three DISTINCT ids across acquire/release cycles")
var mgr = lease_manager_new()
val pid = rt_getpid()
val a = try_acquire_exclusive(mgr, pid, 30000i64)
release_lease(mgr, a.lease_id)
val b = try_acquire_exclusive(mgr, pid, 30000i64)
release_lease(mgr, b.lease_id)
val c = try_acquire_exclusive(mgr, pid, 30000i64)
val a_id = a.lease_id
val b_id = b.lease_id
val c_id = c.lease_id
expect(a_id == b_id).to_equal(false)
expect(b_id == c_id).to_equal(false)
expect(a_id == c_id).to_equal(false)
# NEGATIVE CONTROL: text equality must still report `true` for an id
# compared with itself. Without this, an `==` that always answered
# `false` would make the three assertions above vacuous.
expect(a_id == a_id).to_equal(true)
```

</details>

#### advances the counter monotonically (lease-1, lease-2, lease-3)

- advances the counter monotonically (lease-1, lease-2, lease-3)
   - Expected: a.lease_id equals `lease-1`
   - Expected: b.lease_id equals `lease-2`
   - Expected: c.lease_id equals `lease-3`
   - Expected: c.lease_id == "lease-99" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advances the counter monotonically (lease-1, lease-2, lease-3)")
var mgr = lease_manager_new()
val pid = rt_getpid()
val a = try_acquire_exclusive(mgr, pid, 30000i64)
release_lease(mgr, a.lease_id)
val b = try_acquire_exclusive(mgr, pid, 30000i64)
release_lease(mgr, b.lease_id)
val c = try_acquire_exclusive(mgr, pid, 30000i64)
expect(a.lease_id).to_equal("lease-1")
expect(b.lease_id).to_equal("lease-2")
expect(c.lease_id).to_equal("lease-3")
# NEGATIVE CONTROL: an id the manager never issued must NOT match,
# so `to_equal` is not trivially satisfied.
expect(c.lease_id == "lease-99").to_equal(false)
```

</details>

#### keeps ids distinct across two INDEPENDENT managers' own sequences

- keeps ids distinct across two INDEPENDENT managers' own sequences
   - Expected: x.ok is true
   - Expected: y.ok is true
   - Expected: active_lease_count(m1) equals `1i64`
   - Expected: active_lease_count(m2) equals `1i64`
   - Expected: active_lease_count(m1) == 2i64 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps ids distinct across two INDEPENDENT managers' own sequences")
# Absence control on cross-contamination: a second manager starts its
# own sequence at lease-1 and does NOT see the first manager's leases.
var m1 = lease_manager_new()
var m2 = lease_manager_new()
val pid = rt_getpid()
val x = try_acquire_exclusive(m1, pid, 30000i64)
val y = try_acquire_exclusive(m2, pid, 30000i64)
expect(x.ok).to_equal(true)
expect(y.ok).to_equal(true)
expect(active_lease_count(m1)).to_equal(1i64)
expect(active_lease_count(m2)).to_equal(1i64)
# NEGATIVE CONTROL: m1 must NOT have absorbed m2's lease.
expect(active_lease_count(m1) == 2i64).to_equal(false)
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

- Canonical SPipe generation for source `c2e522434c3664a5a9270ce8de403d35111821f0c3cf4d2a12270be7f2065261`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2e522434c3664a5a9270ce8de403d35111821f0c3cf4d2a12270be7f2065261`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2e522434c3664a5a9270ce8de403d35111821f0c3cf4d2a12270be7f2065261`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/service/lease_grant_spec.spl
mirror: doc/06_spec/01_unit/lib/service/lease_grant_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/service/lease_grant_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/service/lease_grant_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/service/lease_grant_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'grants exclusive lease when no leases are held' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/service/lease_grant_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects second exclusive lease while first is held' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/service/lease_grant_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'grants exclusive after release' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
