# Notifications Vertical — scenario over the durable store

> The notifications vertical of the Simple Enterprise Suite, exercised against the durable enterprise store: an operator enqueues a notification (recipient, channel, template_key, payload) at status "pending", the pending fold lists it, and mark_sent transitions it to "sent". Every mutation runs the frozen guarded sequence (session -> rbac -> validation -> idempotency -> effects in one UoW) and chains a sha256 audit record.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Notifications Vertical — scenario over the durable store

The notifications vertical of the Simple Enterprise Suite, exercised against the durable enterprise store: an operator enqueues a notification (recipient, channel, template_key, payload) at status "pending", the pending fold lists it, and mark_sent transitions it to "sent". Every mutation runs the frozen guarded sequence (session -> rbac -> validation -> idempotency -> effects in one UoW) and chains a sha256 audit record.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_sync_mut/enterprise_notifications_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The notifications vertical of the Simple Enterprise Suite, exercised against
the durable enterprise store: an operator enqueues a notification (recipient,
channel, template_key, payload) at status "pending", the pending fold lists it,
and mark_sent transitions it to "sent". Every mutation runs the frozen guarded
sequence (session -> rbac -> validation -> idempotency -> effects in one UoW)
and chains a sha256 audit record.

## Guarded sequence proven here (reproduce-first for each denial)

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| rbac | forbidden | an unauthorized role cannot enqueue |
| session | invalid-session | a cross-tenant forged session is rejected outright |
| validation | invalid-transition | marking an already-sent notification sent again (double-send) |
| idempotency | duplicate-key | replay returns recorded result, exactly one effect |
| tenancy | invalid-record | tenant B cannot mark tenant A's notification sent |

## Invariants

- current status is a pure fold over the insert-only status stream (never UPDATE);
- a double-send is denied with the closed-set reason invalid-transition;
- a replayed command produces exactly one effect (pending fold unchanged);
- the session tenant is authority — a cross-tenant session is rejected outright.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (W21-A).

## Scenarios

### notifications vertical — one complete outbox flow end to end

#### enqueue -> pending -> mark_sent with a pure pending fold

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- enqueue -> pending -> mark_sent with a pure pending fold
- Open a clean store
- Enqueue a notification — status folds to 'pending'
   - Expected: enq.reason equals `accepted`
   - Expected: notify_status_of(store, "tenant-a", "n-1") equals `pending`
- The pending fold lists exactly the enqueued notification
   - Expected: pend.len() equals `1`
   - Expected: pend[0] equals `n-1`
- Mark it sent — status folds to 'sent'
   - Expected: sent.reason equals `accepted`
   - Expected: notify_status_of(store, "tenant-a", "n-1") equals `sent`
- The pending fold is now empty
   - Expected: notify_pending(store, "tenant-a").len() equals `0`
- The audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("enqueue -> pending -> mark_sent with a pure pending fold")
step("Open a clean store")
val store = fresh_store("e2e")
val t = tenant_a()
val op = op_a()
val s = session_for(op, t)

step("Enqueue a notification — status folds to 'pending'")
val enq = notify_enqueue(store, s, t, op, envelope("enq-k1", "notify.enqueue"), "n-1", "alice@example.com", "email", "welcome", "{}")
expect(enq.reason).to_equal("accepted")
expect(reason_allowed(enq.reason)).to_be(true)
expect(notify_status_of(store, "tenant-a", "n-1")).to_equal("pending")

step("The pending fold lists exactly the enqueued notification")
val pend = notify_pending(store, "tenant-a")
expect(pend.len()).to_equal(1)
expect(pend[0]).to_equal("n-1")

step("Mark it sent — status folds to 'sent'")
val sent = notify_mark_sent(store, s, t, op, envelope("snd-k1", "notify.mark_sent"), "n-1")
expect(sent.reason).to_equal("accepted")
expect(notify_status_of(store, "tenant-a", "n-1")).to_equal("sent")

step("The pending fold is now empty")
expect(notify_pending(store, "tenant-a").len()).to_equal(0)

step("The audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

### notifications vertical — rbac denies an unauthorized actor

#### reproduce: a viewer cannot enqueue (forbidden)

- reproduce: a viewer cannot enqueue (forbidden)
- Attempt notify_enqueue as a viewer role
   - Expected: r.reason equals `forbidden`
- No notification was created
   - Expected: notify_status_of(store, "tenant-a", "n-x") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: a viewer cannot enqueue (forbidden)")
val store = fresh_store("rbac")
val t = tenant_a()
val viewer = viewer_a()
step("Attempt notify_enqueue as a viewer role")
val r = notify_enqueue(store, session_for(viewer, t), t, viewer, envelope("k-r", "notify.enqueue"), "n-x", "bob@example.com", "sms", "alert", "{}")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("forbidden")
expect(reason_allowed(r.reason)).to_be(true)
step("No notification was created")
expect(notify_status_of(store, "tenant-a", "n-x")).to_equal("")
store_close(store)
```

</details>

### notifications vertical — a double-send is invalid-transition

#### reproduce: marking an already-sent notification sent again is invalid-transition

- reproduce: marking an already-sent notification sent again is invalid-transition
- Mark sent again with a FRESH key — the notification is no longer 'pending'
   - Expected: again.reason equals `invalid-transition`
- Status is unchanged — still 'sent'
   - Expected: notify_status_of(store, "tenant-a", "n-2") equals `sent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: marking an already-sent notification sent again is invalid-transition")
val store = fresh_store("double_send")
val t = tenant_a()
val op = op_a()
val s = session_for(op, t)
notify_enqueue(store, s, t, op, envelope("e", "notify.enqueue"), "n-2", "carol@example.com", "email", "receipt", "{}")
notify_mark_sent(store, s, t, op, envelope("m", "notify.mark_sent"), "n-2")
step("Mark sent again with a FRESH key — the notification is no longer 'pending'")
val again = notify_mark_sent(store, s, t, op, envelope("m2", "notify.mark_sent"), "n-2")
expect(again.ok).to_be(false)
expect(again.reason).to_equal("invalid-transition")
expect(reason_allowed(again.reason)).to_be(true)
step("Status is unchanged — still 'sent'")
expect(notify_status_of(store, "tenant-a", "n-2")).to_equal("sent")
store_close(store)
```

</details>

#### reproduce: marking an unknown notification sent is invalid-record

- reproduce: marking an unknown notification sent is invalid-record
- Mark sent a notification that was never enqueued
   - Expected: r.reason equals `invalid-record`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reproduce: marking an unknown notification sent is invalid-record")
val store = fresh_store("unknown")
val t = tenant_a()
val op = op_a()
val s = session_for(op, t)
step("Mark sent a notification that was never enqueued")
val r = notify_mark_sent(store, s, t, op, envelope("u", "notify.mark_sent"), "ghost")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-record")
store_close(store)
```

</details>

### notifications vertical — idempotent replay produces exactly one effect

#### replaying an enqueue changes nothing

- replaying an enqueue changes nothing
- Enqueue once
   - Expected: first.reason equals `accepted`
- Replay the SAME idempotency key
   - Expected: replay.reason equals `duplicate-key`
   - Expected: replay.detail equals `n-3`
- No second effect — pending fold and outbox unchanged
   - Expected: notify_pending(store, "tenant-a").len() equals `pending_after_first`
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("replaying an enqueue changes nothing")
val store = fresh_store("replay")
val t = tenant_a()
val op = op_a()
val s = session_for(op, t)

step("Enqueue once")
val first = notify_enqueue(store, s, t, op, envelope("same-key", "notify.enqueue"), "n-3", "dan@example.com", "push", "promo", "{}")
expect(first.reason).to_equal("accepted")
val pending_after_first = notify_pending(store, "tenant-a").len()
val outbox_after_first = outbox_pending(store, "tenant-a").len()

step("Replay the SAME idempotency key")
val replay = notify_enqueue(store, s, t, op, envelope("same-key", "notify.enqueue"), "n-3", "dan@example.com", "push", "promo", "{}")
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(replay.detail).to_equal("n-3")

step("No second effect — pending fold and outbox unchanged")
expect(notify_pending(store, "tenant-a").len()).to_equal(pending_after_first)
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after_first)
store_close(store)
```

</details>

### notifications vertical — tenant isolation

#### tenant B cannot see or mutate tenant A's notifications

- tenant B cannot see or mutate tenant A's notifications
- Tenant B sees no status for tenant A's notification
   - Expected: notify_status_of(store, "tenant-b", "n-a") equals ``
- Tenant B's pending fold is empty
   - Expected: notify_pending(store, "tenant-b").len() equals `0`
- A tenant-B op cannot mark tenant A's notification sent — invalid-record in B's scope
   - Expected: r.reason equals `invalid-record`
- A cross-tenant session (B token presented with A as authority) is rejected outright
   - Expected: r2.reason equals `invalid-session`
- Tenant A's notification is untouched — still 'pending'
   - Expected: notify_status_of(store, "tenant-a", "n-a") equals `pending`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tenant B cannot see or mutate tenant A's notifications")
val store = fresh_store("isolation")
val ta = tenant_a()
val op = op_a()
val sa = session_for(op, ta)
notify_enqueue(store, sa, ta, op, envelope("na", "notify.enqueue"), "n-a", "eve@example.com", "email", "welcome", "{}")

step("Tenant B sees no status for tenant A's notification")
expect(notify_status_of(store, "tenant-b", "n-a")).to_equal("")
step("Tenant B's pending fold is empty")
expect(notify_pending(store, "tenant-b").len()).to_equal(0)

step("A tenant-B op cannot mark tenant A's notification sent — invalid-record in B's scope")
val tb = tenant_b()
val op_b = ActorContext(actor_id: "op-b", role: "sales")
val sb = session_for(op_b, tb)
val r = notify_mark_sent(store, sb, tb, op_b, envelope("mb", "notify.mark_sent"), "n-a")
expect(r.ok).to_be(false)
expect(r.reason).to_equal("invalid-record")

step("A cross-tenant session (B token presented with A as authority) is rejected outright")
val forged = SessionContext(token: "tok-op-b", actor_id: "op-b", tenant_id: "tenant-b", active: true)
val r2 = notify_mark_sent(store, forged, ta, op_b, envelope("mb2", "notify.mark_sent"), "n-a")
expect(r2.reason).to_equal("invalid-session")

step("Tenant A's notification is untouched — still 'pending'")
expect(notify_status_of(store, "tenant-a", "n-a")).to_equal("pending")
store_close(store)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `83baf59a1e8565f42ee1a43ba752476e73b01b33da2b5a946c36a38daf3d4271`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `83baf59a1e8565f42ee1a43ba752476e73b01b33da2b5a946c36a38daf3d4271`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `83baf59a1e8565f42ee1a43ba752476e73b01b33da2b5a946c36a38daf3d4271`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/enterprise_notifications_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_notifications_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_notifications_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/enterprise_notifications_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/enterprise_notifications_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/enterprise_notifications_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enqueue -> pending -> mark_sent with a pure pending fold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_notifications_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reproduce: a viewer cannot enqueue (forbidden)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/enterprise_notifications_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reproduce: marking an already-sent notification sent again is invalid-transition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
