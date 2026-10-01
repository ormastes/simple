# Container + Multi-Tenant Specification (OCap Privilege — S5/S6)

> S5 — a **Container** is the shape of a CSpace (cspace + sub-budget + label namespace) owned by EXACTLY ONE session. It captures the owner session's epoch, so a session teardown (epoch bump) revokes every container it owns in O(1): a container cap dies with its session. Cross-session cowork uses **escrow_cap** — the "scheduler-LLM hands ticketing-LLM a one-shot create-ticket cap" flow: a SINGLE-USE cap minted into the RECEIVER's arena (bound to the receiver's epoch), consumed on first use, and MONOTONIC (never exceeds the sender's current).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Container + Multi-Tenant Specification (OCap Privilege — S5/S6)

S5 — a **Container** is the shape of a CSpace (cspace + sub-budget + label namespace) owned by EXACTLY ONE session. It captures the owner session's epoch, so a session teardown (epoch bump) revokes every container it owns in O(1): a container cap dies with its session. Cross-session cowork uses **escrow_cap** — the "scheduler-LLM hands ticketing-LLM a one-shot create-ticket cap" flow: a SINGLE-USE cap minted into the RECEIVER's arena (bound to the receiver's epoch), consumed on first use, and MONOTONIC (never exceeds the sender's current).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-OCAP-S5 #OS-OCAP-S6 |
| Category | Runtime / Security |
| Difficulty | 4/5 |
| Status | Implemented |
| Plan | doc/04_architecture/os/security/ocap_privilege_architecture.md (§P4, §17-19) |
| Design | doc/01_research/os/security/session_subprivilege_hierarchy_research.md |
| Source | `test/01_unit/os/security/container_multitenant_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

S5 — a **Container** is the shape of a CSpace (cspace + sub-budget + label
namespace) owned by EXACTLY ONE session. It captures the owner session's epoch,
so a session teardown (epoch bump) revokes every container it owns in O(1): a
container cap dies with its session. Cross-session cowork uses **escrow_cap** —
the "scheduler-LLM hands ticketing-LLM a one-shot create-ticket cap" flow: a
SINGLE-USE cap minted into the RECEIVER's arena (bound to the receiver's epoch),
consumed on first use, and MONOTONIC (never exceeds the sender's current).

S6 — a **multi-tenant tree** System → Tenant → User with DISJOINT arenas +
per-node budget quota. A Tenant's User children cannot see or exceed the Tenant
ceiling (structural, by capability designation — not ACL); teardown of a Tenant
cascades to all its descendants via the session_teardown DFS epoch bump; a child
can never be funded above its parent's budget.

The gate asserts:
  - a container's cspace ⊆ its owner session (and a wider cspace is rejected);
  - a container dies the instant its owner session is torn down;
  - an escrow cap is single-use (a second consume is denied);
  - an escrow cap is monotonic (a cap the sender does not hold is rejected);
  - two Tenants have disjoint arenas (Tenant-A's User cannot reach Tenant-B caps);
  - a Tenant's child cannot exceed the Tenant ceiling (fail closed);
  - Tenant teardown cascades to ALL descendants (and not to sibling tenants);
  - per-node budget quota is enforced (a child cannot exceed the parent budget).

## Scenarios

### container: cspace is bounded by the owner session

#### accepts a container whose cspace is within the owner's current

- accepts a container whose cspace is within the owner's current
   - Expected: c_opt != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a container whose cspace is within the owner's current")
var mgr = CapabilityManager.new()
val sys = mgr.open_system("system", root_caps(), 1000u64)
val c_opt = mgr.create_container(sys.id, caps1(_fr("/data"), 20u64, 30u64), 500u64, ["data"])
expect(c_opt != nil).to_equal(true)
```

</details>

#### the container's cspace IS a subset of the owner session current

- the container's cspace IS a subset of the owner session current
   - Expected: c_opt != nil is true
   - Expected: capset_subset(c.cspace, sys.current) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the container's cspace IS a subset of the owner session current")
var mgr = CapabilityManager.new()
val sys = mgr.open_system("system", root_caps(), 1000u64)
val c_opt = mgr.create_container(sys.id, caps1(_fr("/data"), 20u64, 30u64), 500u64, ["data"])
expect(c_opt != nil).to_equal(true)
val c = c_opt
expect(capset_subset(c.cspace, sys.current)).to_equal(true)
```

</details>

#### REJECTS a container whose cspace exceeds the owner (NetRaw not held)

- REJECTS a container whose cspace exceeds the owner (NetRaw not held)
   - Expected: c_opt equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS a container whose cspace exceeds the owner (NetRaw not held)")
var mgr = CapabilityManager.new()
val sys = mgr.open_system("system", root_caps(), 1000u64)
val c_opt = mgr.create_container(sys.id, caps1(_netraw(), 20u64, 30u64), 100u64, ["raw"])
expect(c_opt).to_equal(nil)
```

</details>

#### REJECTS a container whose budget exceeds the owner's budget (quota)

- REJECTS a container whose budget exceeds the owner's budget (quota)
   - Expected: c_opt equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS a container whose budget exceeds the owner's budget (quota)")
var mgr = CapabilityManager.new()
val sys = mgr.open_system("system", root_caps(), 1000u64)
val c_opt = mgr.create_container(sys.id, caps1(_fr("/data"), 20u64, 30u64), 2000u64, ["data"])
expect(c_opt).to_equal(nil)
```

</details>

#### REJECTS an ambient-full cspace under a concrete owner (vacuous-subset escalation)

- REJECTS an ambient-full cspace under a concrete owner (vacuous-subset escalation)
   - Expected: c_opt equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS an ambient-full cspace under a concrete owner (vacuous-subset escalation)")
# An ambient-full cspace (is_pledged:false + zero tokens) authorizes
# EVERYTHING; capset_subset must not vacuously accept it under a narrow
# owner (same OCap escalation class as create_child_session). Closed at
# root in session_types.capset_subset.
var mgr = CapabilityManager.new()
val sys = mgr.open_system("system", root_caps(), 1000u64)
val c_opt = mgr.create_container(sys.id, CapabilitySet.full(), 100u64, ["all"])
expect(c_opt).to_equal(nil)
```

</details>

### container: dies with its owning session (epoch-bound)
_A container inherits the owner session's epoch; teardown revokes it O(1)._

#### container is live before teardown and dead after owner teardown

- container is live before teardown and dead after owner teardown
   - Expected: c_opt != nil is true
   - Expected: mgr.container_live(c) is true
   - Expected: mgr.container_live(c) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("container is live before teardown and dead after owner teardown")
var mgr = CapabilityManager.new()
val sys = mgr.open_system("system", root_caps(), 1000u64)
val c_opt = mgr.create_container(sys.id, caps1(_fr("/data"), 20u64, 30u64), 500u64, ["data"])
expect(c_opt != nil).to_equal(true)
val c = c_opt
expect(mgr.container_live(c)).to_equal(true)
mgr.session_teardown(sys)
expect(mgr.container_live(c)).to_equal(false)
```

</details>

### escrow_cap: single-use, monotonic cross-session cap hand-off
_A scheduler session hands a ticketing session a one-shot create-ticket cap._

#### escrow into the receiver succeeds when the sender holds the cap

- escrow into the receiver succeeds when the sender holds the cap
   - Expected: e_opt != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escrow into the receiver succeeds when the sender holds the cap")
var mgr = CapabilityManager.new()
val sched = mgr.login("scheduler", caps1(_fw("/tickets"), 40u64, 50u64))
val ticket = mgr.login("ticketing", caps1(_fr("/tickets"), 41u64, 51u64))
val e_opt = mgr.escrow_cap(sched.id, ticket.id, _tok(_fw("/tickets"), 60u64, 70u64))
expect(e_opt != nil).to_equal(true)
```

</details>

#### the escrow cap is single-use: first consume returns it, second is DENIED

- the escrow cap is single-use: first consume returns it, second is DENIED
   - Expected: e_opt != nil is true
   - Expected: first != nil is true
   - Expected: second equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the escrow cap is single-use: first consume returns it, second is DENIED")
var mgr = CapabilityManager.new()
val sched = mgr.login("scheduler", caps1(_fw("/tickets"), 40u64, 50u64))
val ticket = mgr.login("ticketing", caps1(_fr("/tickets"), 41u64, 51u64))
val e_opt = mgr.escrow_cap(sched.id, ticket.id, _tok(_fw("/tickets"), 60u64, 70u64))
expect(e_opt != nil).to_equal(true)
val e = e_opt
val first = mgr.consume_escrow(e.id, ticket.id)
expect(first != nil).to_equal(true)
val second = mgr.consume_escrow(e.id, ticket.id)
expect(second).to_equal(nil)
```

</details>

#### escrow is MONOTONIC: a kind the sender does not hold is rejected

- escrow is MONOTONIC: a kind the sender does not hold is rejected
   - Expected: e_opt equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escrow is MONOTONIC: a kind the sender does not hold is rejected")
var mgr = CapabilityManager.new()
val sched = mgr.login("scheduler", caps1(_fw("/tickets"), 40u64, 50u64))
val ticket = mgr.login("ticketing", caps1(_fr("/tickets"), 41u64, 51u64))
val e_opt = mgr.escrow_cap(sched.id, ticket.id, _tok(_netraw(), 60u64, 70u64))
expect(e_opt).to_equal(nil)
```

</details>

#### escrow CANNOT exceed the sender: a wider path than the sender holds is rejected

- escrow CANNOT exceed the sender: a wider path than the sender holds is rejected
   - Expected: e_opt equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escrow CANNOT exceed the sender: a wider path than the sender holds is rejected")
var mgr = CapabilityManager.new()
# sender holds only /tickets write; escrowing write on "/" (wider) is denied
val sched = mgr.login("scheduler", caps1(_fw("/tickets"), 40u64, 50u64))
val ticket = mgr.login("ticketing", caps1(_fr("/tickets"), 41u64, 51u64))
val e_opt = mgr.escrow_cap(sched.id, ticket.id, _tok(_fw("/"), 60u64, 70u64))
expect(e_opt).to_equal(nil)
```

</details>

#### a wrong receiver cannot consume the escrow

- a wrong receiver cannot consume the escrow
   - Expected: e_opt != nil is true
   - Expected: wrong equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a wrong receiver cannot consume the escrow")
var mgr = CapabilityManager.new()
val sched = mgr.login("scheduler", caps1(_fw("/tickets"), 40u64, 50u64))
val ticket = mgr.login("ticketing", caps1(_fr("/tickets"), 41u64, 51u64))
val e_opt = mgr.escrow_cap(sched.id, ticket.id, _tok(_fw("/tickets"), 60u64, 70u64))
expect(e_opt != nil).to_equal(true)
val e = e_opt
val wrong = mgr.consume_escrow(e.id, sched.id)
expect(wrong).to_equal(nil)
```

</details>

#### the escrow dies with the receiver: consume denied after receiver teardown

- the escrow dies with the receiver: consume denied after receiver teardown
   - Expected: e_opt != nil is true
   - Expected: after equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the escrow dies with the receiver: consume denied after receiver teardown")
var mgr = CapabilityManager.new()
val sched = mgr.login("scheduler", caps1(_fw("/tickets"), 40u64, 50u64))
val ticket = mgr.login("ticketing", caps1(_fr("/tickets"), 41u64, 51u64))
val e_opt = mgr.escrow_cap(sched.id, ticket.id, _tok(_fw("/tickets"), 60u64, 70u64))
expect(e_opt != nil).to_equal(true)
val e = e_opt
mgr.session_teardown(ticket)
val after = mgr.consume_escrow(e.id, ticket.id)
expect(after).to_equal(nil)
```

</details>

### multi-tenant: two tenants have disjoint arenas
_Isolation is structural (by capability designation), not by ACL._

#### Tenant-A's User can reach Tenant-A caps but NOT Tenant-B caps

- Tenant-A's User can reach Tenant-A caps but NOT Tenant-B caps
   - Expected: ta_opt != nil is true
   - Expected: tb_opt != nil is true
   - Expected: ua_opt != nil is true
   - Expected: ua.current.has(_fr("/tenantA")) is true
   - Expected: ua.current.has(_fr("/tenantB")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Tenant-A's User can reach Tenant-A caps but NOT Tenant-B caps")
var mgr = CapabilityManager.new()
val sys = mgr.open_system("system", root_caps(), 1000u64)
val ta_opt = mgr.create_child_quota(sys.id, SessionKind.Tenant, "acme", caps1(_fr("/tenantA"), 100u64, 110u64), caps1(_fr("/tenantA"), 100u64, 110u64), 400u64)
val tb_opt = mgr.create_child_quota(sys.id, SessionKind.Tenant, "globex", caps1(_fr("/tenantB"), 101u64, 111u64), caps1(_fr("/tenantB"), 101u64, 111u64), 400u64)
expect(ta_opt != nil).to_equal(true)
expect(tb_opt != nil).to_equal(true)
val ta = ta_opt
val ua_opt = mgr.create_child_quota(ta.id, SessionKind.User, "alice", caps1(_fr("/tenantA"), 102u64, 112u64), caps1(_fr("/tenantA"), 102u64, 112u64), 200u64)
expect(ua_opt != nil).to_equal(true)
val ua = ua_opt
expect(ua.current.has(_fr("/tenantA"))).to_equal(true)
expect(ua.current.has(_fr("/tenantB"))).to_equal(false)
```

</details>

### multi-tenant: a child cannot exceed the Tenant ceiling
_ceiling(child) ⊆ current(parent) — fail closed._

#### REJECTS a User whose ceiling is wider than the Tenant's current

- REJECTS a User whose ceiling is wider than the Tenant's current
   - Expected: ta_opt != nil is true
   - Expected: over_opt equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS a User whose ceiling is wider than the Tenant's current")
var mgr = CapabilityManager.new()
val sys = mgr.open_system("system", root_caps(), 1000u64)
val ta_opt = mgr.create_child_quota(sys.id, SessionKind.Tenant, "acme", caps1(_fr("/tenantA"), 100u64, 110u64), caps1(_fr("/tenantA"), 100u64, 110u64), 400u64)
expect(ta_opt != nil).to_equal(true)
val ta = ta_opt
# A User asking for read on "/" (wider than the tenant's "/tenantA") is denied.
val over_opt = mgr.create_child_quota(ta.id, SessionKind.User, "alice", caps1(_fr("/"), 103u64, 113u64), caps1(_fr("/"), 103u64, 113u64), 100u64)
expect(over_opt).to_equal(nil)
```

</details>

### multi-tenant: per-node budget quota (child budget <= parent)
_A child can never be funded above its parent's budget._

#### REJECTS a child whose budget exceeds the parent budget

- REJECTS a child whose budget exceeds the parent budget
   - Expected: ta_opt != nil is true
   - Expected: over_opt equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS a child whose budget exceeds the parent budget")
var mgr = CapabilityManager.new()
val sys = mgr.open_system("system", root_caps(), 1000u64)
val ta_opt = mgr.create_child_quota(sys.id, SessionKind.Tenant, "acme", caps1(_fr("/tenantA"), 100u64, 110u64), caps1(_fr("/tenantA"), 100u64, 110u64), 400u64)
expect(ta_opt != nil).to_equal(true)
val ta = ta_opt
val over_opt = mgr.create_child_quota(ta.id, SessionKind.User, "alice", caps1(_fr("/tenantA"), 104u64, 114u64), caps1(_fr("/tenantA"), 104u64, 114u64), 500u64)
expect(over_opt).to_equal(nil)
```

</details>

#### ACCEPTS a child whose budget is within the parent budget

- ACCEPTS a child whose budget is within the parent budget
   - Expected: ta_opt != nil is true
   - Expected: ok_opt != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ACCEPTS a child whose budget is within the parent budget")
var mgr = CapabilityManager.new()
val sys = mgr.open_system("system", root_caps(), 1000u64)
val ta_opt = mgr.create_child_quota(sys.id, SessionKind.Tenant, "acme", caps1(_fr("/tenantA"), 100u64, 110u64), caps1(_fr("/tenantA"), 100u64, 110u64), 400u64)
expect(ta_opt != nil).to_equal(true)
val ta = ta_opt
val ok_opt = mgr.create_child_quota(ta.id, SessionKind.User, "alice", caps1(_fr("/tenantA"), 105u64, 115u64), caps1(_fr("/tenantA"), 105u64, 115u64), 300u64)
expect(ok_opt != nil).to_equal(true)
```

</details>

### multi-tenant: Tenant teardown cascades to all descendants

#### a User bound cap is dead and the User session sealed after Tenant teardown

- a User bound cap is dead and the User session sealed after Tenant teardown
   - Expected: ta_opt != nil is true
   - Expected: tb_opt != nil is true
   - Expected: ua_opt != nil is true
   - Expected: mgr.check(alice_task, _fr("/tenantA")) is true
   - Expected: mgr.check(alice_task, _fr("/tenantA")) is false
   - Expected: sealed_of(mgr.session_of(ua.id)) is true
   - Expected: sealed_of(mgr.session_of(ta.id)) is true
   - Expected: sealed_of(mgr.session_of(tb.id)) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a User bound cap is dead and the User session sealed after Tenant teardown")
var mgr = CapabilityManager.new()
val sys = mgr.open_system("system", root_caps(), 1000u64)
val ta_opt = mgr.create_child_quota(sys.id, SessionKind.Tenant, "acme", caps1(_fr("/tenantA"), 100u64, 110u64), caps1(_fr("/tenantA"), 100u64, 110u64), 400u64)
val tb_opt = mgr.create_child_quota(sys.id, SessionKind.Tenant, "globex", caps1(_fr("/tenantB"), 101u64, 111u64), caps1(_fr("/tenantB"), 101u64, 111u64), 400u64)
expect(ta_opt != nil).to_equal(true)
expect(tb_opt != nil).to_equal(true)
val ta = ta_opt
val tb = tb_opt
val ua_opt = mgr.create_child_quota(ta.id, SessionKind.User, "alice", caps1(_fr("/tenantA"), 102u64, 112u64), caps1(_fr("/tenantA"), 102u64, 112u64), 200u64)
expect(ua_opt != nil).to_equal(true)
val ua = ua_opt
val alice_task = TaskId(id: 77)
mgr.install_sandbox_capability_set(alice_task, ua.current)
mgr.bind_task_to_session(alice_task, ua.id)
expect(mgr.check(alice_task, _fr("/tenantA"))).to_equal(true)
mgr.session_teardown(ta)
expect(mgr.check(alice_task, _fr("/tenantA"))).to_equal(false)
expect(sealed_of(mgr.session_of(ua.id))).to_equal(true)
expect(sealed_of(mgr.session_of(ta.id))).to_equal(true)
# Disjoint: the sibling tenant is untouched.
expect(sealed_of(mgr.session_of(tb.id))).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/04_architecture/os/security/ocap_privilege_architecture.md (§P4, §17-19)`
- **Design:** `doc/01_research/os/security/session_subprivilege_hierarchy_research.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `64ba73d2e936a66cb67341d9b6d39558237b0131f81e11c71c20bfe08b4840f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `64ba73d2e936a66cb67341d9b6d39558237b0131f81e11c71c20bfe08b4840f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `64ba73d2e936a66cb67341d9b6d39558237b0131f81e11c71c20bfe08b4840f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/security/container_multitenant_spec.spl
mirror: doc/06_spec/01_unit/os/security/container_multitenant_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/security/container_multitenant_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/security/container_multitenant_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/security/container_multitenant_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a container whose cspace is within the owner's current' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/security/container_multitenant_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the container's cspace IS a subset of the owner session current' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/security/container_multitenant_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REJECTS a container whose cspace exceeds the owner (NetRaw not held)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
