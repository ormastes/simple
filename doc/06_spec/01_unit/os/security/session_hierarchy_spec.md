# Session Hierarchy Specification (OCap Privilege — S1/S2/S3)

> The session foundation of the OCap privilege model: an authenticated `login` mints a root **User** session whose ceiling == current == the principal's granted capabilities. A **SubRole** drops into an irreversibly narrowed slice of its parent (AND-mask via pledge) — it can never regain a dropped cap and can never exceed the parent ceiling. **Teardown** DFS-seals a session subtree and bumps each epoch, which bulk-revokes every capability bound to those sessions in O(1) (no per-token walk) — this is what SSH disconnect must call.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Hierarchy Specification (OCap Privilege — S1/S2/S3)

The session foundation of the OCap privilege model: an authenticated `login` mints a root **User** session whose ceiling == current == the principal's granted capabilities. A **SubRole** drops into an irreversibly narrowed slice of its parent (AND-mask via pledge) — it can never regain a dropped cap and can never exceed the parent ceiling. **Teardown** DFS-seals a session subtree and bumps each epoch, which bulk-revokes every capability bound to those sessions in O(1) (no per-token walk) — this is what SSH disconnect must call.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-OCAP-S1 #OS-OCAP-S2 #OS-OCAP-S3 |
| Category | Runtime / Security |
| Difficulty | 4/5 |
| Status | Implemented |
| Plan | doc/04_architecture/os/security/ocap_privilege_architecture.md |
| Design | doc/01_research/os/security/session_subprivilege_hierarchy_research.md |
| Source | `test/01_unit/os/security/session_hierarchy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The session foundation of the OCap privilege model: an authenticated `login`
mints a root **User** session whose ceiling == current == the principal's
granted capabilities. A **SubRole** drops into an irreversibly narrowed slice
of its parent (AND-mask via pledge) — it can never regain a dropped cap and can
never exceed the parent ceiling. **Teardown** DFS-seals a session subtree and
bumps each epoch, which bulk-revokes every capability bound to those sessions in
O(1) (no per-token walk) — this is what SSH disconnect must call.

The gate asserts:
  - login mints a User session holding the principal's max caps (ceiling+current);
  - two logins are disjoint in both id and epoch;
  - open_subrole cannot regain a dropped cap and cannot exceed the parent ceiling
    (child current ⊆ parent current, monotonic);
  - a child cap is invalidated the instant the parent session epoch bumps
    (teardown cascade seals the whole subtree);
  - ceiling(child) ⊆ current(parent) is enforced at session creation (fail closed);
  - budget is refunded upward on teardown.

## Scenarios

### login: mints a User session with the principal's max caps

#### login session kind is User

- login session kind is User
   - Expected: is_user(s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("login session kind is User")
var mgr = CapabilityManager.new()
val s = mgr.login("alice", make_max_caps())
expect(is_user(s)).to_equal(true)
```

</details>

#### login current holds every granted cap

- login current holds every granted cap
   - Expected: s.current.has(_fr()) is true
   - Expected: s.current.has(_fw()) is true
   - Expected: s.current.has(_spawn()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("login current holds every granted cap")
var mgr = CapabilityManager.new()
val s = mgr.login("alice", make_max_caps())
expect(s.current.has(_fr())).to_equal(true)
expect(s.current.has(_fw())).to_equal(true)
expect(s.current.has(_spawn())).to_equal(true)
```

</details>

#### login ceiling holds the granted caps (ceiling == current)

- login ceiling holds the granted caps (ceiling == current)
   - Expected: s.ceiling.has(_fr()) is true
   - Expected: s.ceiling.has(_spawn()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("login ceiling holds the granted caps (ceiling == current)")
var mgr = CapabilityManager.new()
val s = mgr.login("alice", make_max_caps())
expect(s.ceiling.has(_fr())).to_equal(true)
expect(s.ceiling.has(_spawn())).to_equal(true)
```

</details>

#### login current does NOT hold a cap the principal was not granted

- login current does NOT hold a cap the principal was not granted
   - Expected: s.current.has(_netraw()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("login current does NOT hold a cap the principal was not granted")
var mgr = CapabilityManager.new()
val s = mgr.login("alice", make_max_caps())
expect(s.current.has(_netraw())).to_equal(false)
```

</details>

#### login mints a root session (no parent)

- login mints a root session (no parent)
   - Expected: s.parent equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("login mints a root session (no parent)")
var mgr = CapabilityManager.new()
val s = mgr.login("alice", make_max_caps())
expect(s.parent).to_equal(0u64)
```

</details>

### login: two logins are disjoint sessions

#### two logins get distinct session ids

- two logins get distinct session ids
   - Expected: eq_u64(a.id, b.id) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two logins get distinct session ids")
var mgr = CapabilityManager.new()
val a = mgr.login("alice", make_max_caps())
val b = mgr.login("bob", make_max_caps())
expect(eq_u64(a.id, b.id)).to_equal(false)
```

</details>

#### two logins get distinct epochs

- two logins get distinct epochs
   - Expected: eq_u64(a.epoch, b.epoch) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two logins get distinct epochs")
var mgr = CapabilityManager.new()
val a = mgr.login("alice", make_max_caps())
val b = mgr.login("bob", make_max_caps())
expect(eq_u64(a.epoch, b.epoch)).to_equal(false)
```

</details>

### open_subrole: irreversible sub-privilege drop (monotonic)

#### subrole session kind is SubRole

- subrole session kind is SubRole
   - Expected: is_subrole(sr) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subrole session kind is SubRole")
var mgr = CapabilityManager.new()
val u = mgr.login("alice", make_max_caps())
val sr = mgr.open_subrole(u, [_fr()])
expect(is_subrole(sr)).to_equal(true)
```

</details>

#### subrole keeps a masked-in cap it inherited

- subrole keeps a masked-in cap it inherited
   - Expected: sr.current.has(_fr()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subrole keeps a masked-in cap it inherited")
var mgr = CapabilityManager.new()
val u = mgr.login("alice", make_max_caps())
val sr = mgr.open_subrole(u, [_fr()])
expect(sr.current.has(_fr())).to_equal(true)
```

</details>

#### subrole drops caps outside the mask (write + spawn dropped)

- subrole drops caps outside the mask (write + spawn dropped)
   - Expected: sr.current.has(_fw()) is false
   - Expected: sr.current.has(_spawn()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subrole drops caps outside the mask (write + spawn dropped)")
var mgr = CapabilityManager.new()
val u = mgr.login("alice", make_max_caps())
val sr = mgr.open_subrole(u, [_fr()])
expect(sr.current.has(_fw())).to_equal(false)
expect(sr.current.has(_spawn())).to_equal(false)
```

</details>

#### subrole cannot REGAIN a cap the parent never held (NetRaw)

- subrole cannot REGAIN a cap the parent never held (NetRaw)
   - Expected: sr.current.has(_netraw()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subrole cannot REGAIN a cap the parent never held (NetRaw)")
var mgr = CapabilityManager.new()
val u = mgr.login("alice", make_max_caps())
val sr = mgr.open_subrole(u, [_netraw()])
expect(sr.current.has(_netraw())).to_equal(false)
```

</details>

#### subrole current is a subset of parent current (monotonic)

- subrole current is a subset of parent current (monotonic)
   - Expected: capset_subset(sr.current, u.current) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subrole current is a subset of parent current (monotonic)")
var mgr = CapabilityManager.new()
val u = mgr.login("alice", make_max_caps())
val sr = mgr.open_subrole(u, [_fr()])
expect(capset_subset(sr.current, u.current)).to_equal(true)
```

</details>

#### subrole cannot EXCEED the parent even when the mask over-asks

- subrole cannot EXCEED the parent even when the mask over-asks
   - Expected: sr.current.has(_fr()) is true
   - Expected: sr.current.has(_netraw()) is false
   - Expected: capset_subset(sr.current, u.current) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("subrole cannot EXCEED the parent even when the mask over-asks")
var mgr = CapabilityManager.new()
val u = mgr.login("alice", make_max_caps())
val sr = mgr.open_subrole(u, [_fr(), _netraw()])
expect(sr.current.has(_fr())).to_equal(true)
expect(sr.current.has(_netraw())).to_equal(false)
expect(capset_subset(sr.current, u.current)).to_equal(true)
```

</details>

### session_teardown: epoch cascade invalidates bound caps

#### a bound child cap is live before teardown and dead after parent teardown

- a bound child cap is live before teardown and dead after parent teardown
   - Expected: mgr.check(child_task, _fr()) is true
   - Expected: mgr.check(child_task, _fr()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a bound child cap is live before teardown and dead after parent teardown")
var mgr = CapabilityManager.new()
val u = mgr.login("alice", make_max_caps())
val sr = mgr.open_subrole(u, [_fr()])
val child_task = TaskId(id: 99)
mgr.install_sandbox_capability_set(child_task, sr.current)
mgr.bind_task_to_session(child_task, sr.id)
expect(mgr.check(child_task, _fr())).to_equal(true)
mgr.session_teardown(u)
expect(mgr.check(child_task, _fr())).to_equal(false)
```

</details>

#### teardown seals the whole subtree (parent AND child)

- teardown seals the whole subtree (parent AND child)
   - Expected: sealed_of(mgr.session_of(u.id)) is true
   - Expected: sealed_of(mgr.session_of(sr.id)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("teardown seals the whole subtree (parent AND child)")
var mgr = CapabilityManager.new()
val u = mgr.login("alice", make_max_caps())
val sr = mgr.open_subrole(u, [_fr()])
mgr.session_teardown(u)
expect(sealed_of(mgr.session_of(u.id))).to_equal(true)
expect(sealed_of(mgr.session_of(sr.id))).to_equal(true)
```

</details>

#### teardown bumps the child session epoch (generation revoke)

- teardown bumps the child session epoch (generation revoke)
   - Expected: eq_u64(epoch_of(mgr.session_of(sr.id)), before) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("teardown bumps the child session epoch (generation revoke)")
var mgr = CapabilityManager.new()
val u = mgr.login("alice", make_max_caps())
val sr = mgr.open_subrole(u, [_fr()])
val before = sr.epoch
mgr.session_teardown(u)
expect(eq_u64(epoch_of(mgr.session_of(sr.id)), before)).to_equal(false)
```

</details>

### create_child_session: enforces ceiling(child) subset of current(parent)
_A child can never be minted above its parent — fail closed._

#### REJECTS a child whose ceiling exceeds the parent's current authority

- REJECTS a child whose ceiling exceeds the parent's current authority
   - Expected: res equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS a child whose ceiling exceeds the parent's current authority")
var mgr = CapabilityManager.new()
val u = mgr.login("alice", make_max_caps())
val over = CapabilitySet(caps: [_tok(_netraw(), 9u64, 90u64)], is_pledged: true)
val res = mgr.create_child_session(u.id, SessionKind.SubRole, "alice", over, over, 0u64)
expect(res).to_equal(nil)
```

</details>

#### ACCEPTS a child whose ceiling is within the parent's current authority

- ACCEPTS a child whose ceiling is within the parent's current authority
   - Expected: res != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ACCEPTS a child whose ceiling is within the parent's current authority")
var mgr = CapabilityManager.new()
val u = mgr.login("alice", make_max_caps())
val within = CapabilitySet(caps: [_tok(_fr(), 9u64, 91u64)], is_pledged: true)
val res = mgr.create_child_session(u.id, SessionKind.Tenant, "alice", within, within, 0u64)
expect(res != nil).to_equal(true)
```

</details>

### session_teardown: refunds budget upward
_Freed subtree budget flows back to the teardown root's parent._

#### child budget is refunded to the parent on teardown

- child budget is refunded to the parent on teardown
   - Expected: child_opt != nil is true
   - Expected: budget_of(mgr.session_of(u.id)) equals `500u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("child budget is refunded to the parent on teardown")
var mgr = CapabilityManager.new()
val u = mgr.login("alice", make_max_caps())
val within = CapabilitySet(caps: [_tok(_fr(), 9u64, 91u64)], is_pledged: true)
val child_opt = mgr.create_child_session(u.id, SessionKind.Tenant, "alice", within, within, 500u64)
expect(child_opt != nil).to_equal(true)
val child = child_opt
mgr.session_teardown(child)
expect(budget_of(mgr.session_of(u.id))).to_equal(500u64)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/04_architecture/os/security/ocap_privilege_architecture.md`
- **Design:** `doc/01_research/os/security/session_subprivilege_hierarchy_research.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1206b90abb9b3615e04a78a2c82e62fe908546d5bf700d24ee8489b51b796588`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1206b90abb9b3615e04a78a2c82e62fe908546d5bf700d24ee8489b51b796588`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1206b90abb9b3615e04a78a2c82e62fe908546d5bf700d24ee8489b51b796588`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/security/session_hierarchy_spec.spl
mirror: doc/06_spec/01_unit/os/security/session_hierarchy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/security/session_hierarchy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/security/session_hierarchy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/security/session_hierarchy_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'login session kind is User' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/security/session_hierarchy_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'login current holds every granted cap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/security/session_hierarchy_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'login ceiling holds the granted caps (ceiling == current)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
