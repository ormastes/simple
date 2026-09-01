# Adversarial: Revocation Soundness (OCap Hardening)

> These specs TRY TO USE authority AFTER it was revoked and assert every derived capability FAILS CLOSED.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adversarial: Revocation Soundness (OCap Hardening)

These specs TRY TO USE authority AFTER it was revoked and assert every derived capability FAILS CLOSED.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-OCAP-HARDEN |
| Category | Runtime / Security (adversarial) |
| Difficulty | 4/5 |
| Status | Implemented |
| Plan | doc/04_architecture/os/security/ocap_privilege_architecture.md (§P1) |
| Source | `test/01_unit/os/security/adversarial_revocation_soundness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

These specs TRY TO USE authority AFTER it was revoked and assert every derived
capability FAILS CLOSED.

Requirement 3 (revocation soundness):
  - `revoke_transitive` on a root token kills the WHOLE delegation subtree — no
    use-after-revoke at any depth of the lineage.
  - Revoking a MIDDLE token kills its descendants but leaves ANCESTORS intact
    (revocation flows down the lineage, never up into unrelated authority).
  - A session teardown bumps the session epoch, so every capability bound at the
    stale epoch is denied (generation/epoch staleness).
  - Revocation is idempotent: a second `revoke_transitive` of the same root finds
    nothing to resurrect and the child stays denied.

## Scenarios

### adversarial revocation: no use-after-revoke down a 3-level lineage

#### revoke_transitive(root) denies grandparent, child AND grandchild

- revoke_transitive(root) denies grandparent, child AND grandchild
   - Expected: mgr.check(gp, _calendar_ro()) is true
   - Expected: mgr.check(ch, _calendar_ro()) is true
   - Expected: mgr.check(gc, _calendar_ro()) is true
   - Expected: ch_mint.source_token_ids[0] equals `101u64`
   - Expected: gc_mint.source_token_ids[0] equals `400u64`
   - Expected: mgr.check(gp, _calendar_ro()) is false
   - Expected: mgr.check(ch, _calendar_ro()) is false
   - Expected: mgr.check(gc, _calendar_ro()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("revoke_transitive(root) denies grandparent, child AND grandchild")
var mgr = CapabilityManager.new()
val gp = TaskId(id: 1)
val ch = TaskId(id: 21)
val gc = TaskId(id: 31)
val gp_caps = CapabilitySet(caps: [_tok(_calendar_rw(), 2u64, 101u64, 2)], is_pledged: true)
mgr.install_sandbox_capability_set(gp, gp_caps)
val ch_mint = spawn_with_cspace(gp_caps, _cal_spec(), 21u64, 2000u64, 400u64)
mgr.install_sandbox_capability_set(ch, ch_mint.caps)
val gc_mint = spawn_with_cspace(ch_mint.caps, _cal_spec(), 31u64, 3000u64, 500u64)
mgr.install_sandbox_capability_set(gc, gc_mint.caps)
# All three hold the derived calendar cap before revocation.
expect(mgr.check(gp, _calendar_ro())).to_equal(true)
expect(mgr.check(ch, _calendar_ro())).to_equal(true)
expect(mgr.check(gc, _calendar_ro())).to_equal(true)
# Lineage: child derived from 101, grandchild from 400.
expect(ch_mint.source_token_ids[0]).to_equal(101u64)
expect(gc_mint.source_token_ids[0]).to_equal(400u64)
# Transitive revoke of the ROOT cascades to the whole subtree.
val n = mgr.revoke_transitive(101u64)
expect(n).to_be_greater_than(2)
expect(mgr.check(gp, _calendar_ro())).to_equal(false)
expect(mgr.check(ch, _calendar_ro())).to_equal(false)
expect(mgr.check(gc, _calendar_ro())).to_equal(false)
```

</details>

#### revoking a MIDDLE token kills descendants but spares the ancestor

- revoking a MIDDLE token kills descendants but spares the ancestor
   - Expected: mgr.check(gp, _calendar_ro()) is true
   - Expected: mgr.check(ch, _calendar_ro()) is false
   - Expected: mgr.check(gc, _calendar_ro()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("revoking a MIDDLE token kills descendants but spares the ancestor")
var mgr = CapabilityManager.new()
val gp = TaskId(id: 1)
val ch = TaskId(id: 22)
val gc = TaskId(id: 32)
val gp_caps = CapabilitySet(caps: [_tok(_calendar_rw(), 2u64, 101u64, 2)], is_pledged: true)
mgr.install_sandbox_capability_set(gp, gp_caps)
val ch_mint = spawn_with_cspace(gp_caps, _cal_spec(), 22u64, 2000u64, 400u64)
mgr.install_sandbox_capability_set(ch, ch_mint.caps)
val gc_mint = spawn_with_cspace(ch_mint.caps, _cal_spec(), 32u64, 3000u64, 500u64)
mgr.install_sandbox_capability_set(gc, gc_mint.caps)
# Revoke the MIDDLE (child token 400): grandchild dies, grandparent lives.
val n = mgr.revoke_transitive(400u64)
expect(n).to_be_greater_than(1)
expect(mgr.check(gp, _calendar_ro())).to_equal(true)
expect(mgr.check(ch, _calendar_ro())).to_equal(false)
expect(mgr.check(gc, _calendar_ro())).to_equal(false)
```

</details>

#### revocation is idempotent — a second revoke resurrects nothing

- revocation is idempotent — a second revoke resurrects nothing
   - Expected: mgr.check(ch, _calendar_ro()) is false
   - Expected: n2 equals `0`
   - Expected: mgr.check(ch, _calendar_ro()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("revocation is idempotent — a second revoke resurrects nothing")
var mgr = CapabilityManager.new()
val gp = TaskId(id: 1)
val ch = TaskId(id: 23)
val gp_caps = CapabilitySet(caps: [_tok(_calendar_rw(), 2u64, 101u64, 2)], is_pledged: true)
mgr.install_sandbox_capability_set(gp, gp_caps)
val ch_mint = spawn_with_cspace(gp_caps, _cal_spec(), 23u64, 2000u64, 400u64)
mgr.install_sandbox_capability_set(ch, ch_mint.caps)
val n1 = mgr.revoke_transitive(101u64)
expect(n1).to_be_greater_than(0)
expect(mgr.check(ch, _calendar_ro())).to_equal(false)
# Second revoke of the same root finds nothing left to remove.
val n2 = mgr.revoke_transitive(101u64)
expect(n2).to_equal(0)
expect(mgr.check(ch, _calendar_ro())).to_equal(false)
```

</details>

### adversarial revocation: stale session epoch denies bound caps

#### a session-bound cap is live before teardown and DEAD after

- a session-bound cap is live before teardown and DEAD after
   - Expected: mgr.check(task, _fread_var()) is true
   - Expected: mgr.check(task, _fread_var()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("a session-bound cap is live before teardown and DEAD after")
var mgr = CapabilityManager.new()
val caps = CapabilitySet(caps: [_tok(_fread_var(), 1u64, 60u64, 2)], is_pledged: true)
val sess = mgr.login("alice", caps)
val task = TaskId(id: 77)
mgr.install_sandbox_capability_set(task, caps)
mgr.bind_task_to_session(task, sess.id)
expect(mgr.check(task, _fread_var())).to_equal(true)
mgr.session_teardown(sess)
expect(mgr.check(task, _fread_var())).to_equal(false)
```

</details>

#### the torn-down session stays sealed (no re-open resurrects it)

- the torn-down session stays sealed (no re-open resurrects it)
   - Expected: mgr.check(task, _fread_var()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("the torn-down session stays sealed (no re-open resurrects it)")
var mgr = CapabilityManager.new()
val caps = CapabilitySet(caps: [_tok(_fread_var(), 1u64, 61u64, 2)], is_pledged: true)
val sess = mgr.login("bob", caps)
val task = TaskId(id: 78)
mgr.install_sandbox_capability_set(task, caps)
mgr.bind_task_to_session(task, sess.id)
mgr.session_teardown(sess)
# Re-binding the SAME task to the (now-sealed) session id does not revive it.
mgr.bind_task_to_session(task, sess.id)
expect(mgr.check(task, _fread_var())).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/04_architecture/os/security/ocap_privilege_architecture.md (§P1)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `956a2eff0774f64fb7f14d27ad9abbc1ed078cc7f498ea35213b64a43b128c8f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `956a2eff0774f64fb7f14d27ad9abbc1ed078cc7f498ea35213b64a43b128c8f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `956a2eff0774f64fb7f14d27ad9abbc1ed078cc7f498ea35213b64a43b128c8f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/security/adversarial_revocation_soundness_spec.spl
mirror: doc/06_spec/01_unit/os/security/adversarial_revocation_soundness_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/security/adversarial_revocation_soundness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/security/adversarial_revocation_soundness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/security/adversarial_revocation_soundness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/security/adversarial_revocation_soundness_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'revoke_transitive(root) denies grandparent, child AND grandchild' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/security/adversarial_revocation_soundness_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'revoking a MIDDLE token kills descendants but spares the ancestor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/security/adversarial_revocation_soundness_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'revocation is idempotent — a second revoke resurrects nothing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
