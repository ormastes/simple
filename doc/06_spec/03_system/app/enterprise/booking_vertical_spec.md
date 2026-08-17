# Booking/Rental Vertical — end-to-end reservations over the durable store

> The booking/rental proving vertical of the Simple Enterprise Suite (assessment §7.2, Wave 3): reservable resources in three modes — exclusive-unit, capacity-pool, assigned-seat — with a guarded hold -> confirm -> cancel / no-show lifecycle over the durable enterprise store. Every write runs the frozen guarded sequence (session -> rbac -> validation -> idempotency -> effects in one UoW), identical to the goods-sale vertical.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Booking/Rental Vertical — end-to-end reservations over the durable store

The booking/rental proving vertical of the Simple Enterprise Suite (assessment §7.2, Wave 3): reservable resources in three modes — exclusive-unit, capacity-pool, assigned-seat — with a guarded hold -> confirm -> cancel / no-show lifecycle over the durable enterprise store. Every write runs the frozen guarded sequence (session -> rbac -> validation -> idempotency -> effects in one UoW), identical to the goods-sale vertical.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/03_system/app/enterprise/booking_vertical_spec.spl` |
| Updated | 2026-08-16 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The booking/rental proving vertical of the Simple Enterprise Suite
(assessment §7.2, Wave 3): reservable resources in three modes —
exclusive-unit, capacity-pool, assigned-seat — with a guarded
hold -> confirm -> cancel / no-show lifecycle over the durable
enterprise store. Every write runs the frozen guarded sequence
(session -> rbac -> validation -> idempotency -> effects in one UoW),
identical to the goods-sale vertical.

Time is caller-supplied: every command takes `now_epoch` and the library
performs no wall-clock reads, so hold expiry is fully deterministic here.

## Guarded sequence and overlap policy proven here

| Rung | Denial reason | Scenario |
|------|---------------|----------|
| session | invalid-session | inactive session rejected |
| rbac | forbidden | viewer role cannot hold |
| validation | not-found / invalid-record / conflict | unknown resource, bad range, overlap policy |
| idempotency | duplicate-key | replay returns recorded result, one effect |

Overlap policy per mode:
- exclusive-unit: no overlapping active booking at all;
- capacity-pool: sum of overlapping active quantities <= capacity;
- assigned-seat: a seat may not be taken by an overlapping active booking.

An "active" blocker is a confirmed booking or a NON-expired hold; an
expired hold (expiry <= caller-supplied now) never blocks.

`conflict` is the ONE reason added to the frozen closed reason set in
`std.enterprise_sale.foundation` for this vertical — a structurally valid
command denied because it collides with an active reservation.

## Troubleshooting

- `conflict` on an apparently free slot: check for a live hold — holds
  block until their TTL passes relative to the now_epoch you supply.
- `invalid-record` on confirm: the hold expired (expires <= now) or the
  booking is not in `hold` state.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (v2, W2-D booking vertical).

## Scenarios

### booking vertical — hold, confirm, cancel per mode

#### runs the exclusive-unit lifecycle end to end

- Admin declares an exclusive-unit resource
   - Expected: mk.reason equals `accepted`
   - Expected: booking_resource_mode(store, "tenant-a", "cabin-1").0 equals `exclusive-unit`
- Agent holds [t0+100, t0+200) with a 300s TTL
   - Expected: h.reason equals `accepted`
   - Expected: booking_status(store, "tenant-a", "bk-1") equals `hold`
- Confirm the hold before expiry
   - Expected: c.reason equals `accepted`
   - Expected: booking_status(store, "tenant-a", "bk-1") equals `confirmed`
- Cancel the confirmed booking; a new hold on the slot now succeeds
   - Expected: x.reason equals `accepted`
   - Expected: booking_status(store, "tenant-a", "bk-1") equals `cancelled`
   - Expected: h2.reason equals `accepted`
- Audit chain recomputes end to end


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("e2e_excl")
val t = tenant_a()
val admin = admin_a()
val sa = session_for(admin, t)
step("Admin declares an exclusive-unit resource")
val mk = booking_create_resource(store, sa, t, admin, "cabin-1", "exclusive-unit", 0, "")
expect(mk.reason).to_equal("accepted")
expect(booking_resource_mode(store, "tenant-a", "cabin-1").0).to_equal("exclusive-unit")

step("Agent holds [t0+100, t0+200) with a 300s TTL")
val agent = agent_a()
val ags = session_for(agent, t)
val h = booking_hold(store, ags, t, agent, envelope("ex-h1", "booking.hold"), "bk-1", "cabin-1", t0() + 100, t0() + 200, 1, "", t0(), 300)
expect(h.reason).to_equal("accepted")
expect(booking_status(store, "tenant-a", "bk-1")).to_equal("hold")

step("Confirm the hold before expiry")
val c = booking_confirm(store, ags, t, agent, envelope("ex-c1", "booking.confirm"), "bk-1", t0() + 60)
expect(c.reason).to_equal("accepted")
expect(booking_status(store, "tenant-a", "bk-1")).to_equal("confirmed")

step("Cancel the confirmed booking; a new hold on the slot now succeeds")
val x = booking_cancel(store, ags, t, agent, envelope("ex-x1", "booking.cancel"), "bk-1")
expect(x.reason).to_equal("accepted")
expect(booking_status(store, "tenant-a", "bk-1")).to_equal("cancelled")
val h2 = booking_hold(store, ags, t, agent, envelope("ex-h2", "booking.hold"), "bk-2", "cabin-1", t0() + 100, t0() + 200, 1, "", t0(), 300)
expect(h2.reason).to_equal("accepted")

step("Audit chain recomputes end to end")
expect(audit_verify_chain(store, "tenant-a")).to_be(true)
store_close(store)
```

</details>

#### runs the capacity-pool lifecycle and the assigned-seat lifecycle

- Declare a 10-bike pool and a versioned seat map
   - Expected: booking_create_resource(store, sa, t, admin, "bikes", "capacity-pool", 10, "").reason equals `accepted`
   - Expected: booking_create_resource(store, sa, t, admin, "hall", "assigned-seat", 0, "v1").reason equals `accepted`
- Pool: hold 6 bikes, confirm, then a no-show is recorded
   - Expected: booking_hold(store, ags, t, agent, envelope("p-h1", "booking.hold"), "pool-1", "bikes", t0(), t0() + 100, 6, "", t0(), 300).reason equals `accepted`
   - Expected: booking_confirm(store, ags, t, agent, envelope("p-c1", "booking.confirm"), "pool-1", t0()).reason equals `accepted`
   - Expected: booking_no_show(store, ags, t, agent, envelope("p-n1", "booking.no_show"), "pool-1").reason equals `accepted`
   - Expected: booking_status(store, "tenant-a", "pool-1") equals `no-show`
- Seat: hold seat A1, confirm, cancel
   - Expected: booking_hold(store, ags, t, agent, envelope("s-h1", "booking.hold"), "seat-1", "hall", t0(), t0() + 100, 1, "A1", t0(), 300).reason equals `accepted`
   - Expected: booking_confirm(store, ags, t, agent, envelope("s-c1", "booking.confirm"), "seat-1", t0()).reason equals `accepted`
   - Expected: booking_cancel(store, ags, t, agent, envelope("s-x1", "booking.cancel"), "seat-1").reason equals `accepted`
   - Expected: booking_status(store, "tenant-a", "seat-1") equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("e2e_modes")
val t = tenant_a()
val admin = admin_a()
val sa = session_for(admin, t)
val agent = agent_a()
val ags = session_for(agent, t)
step("Declare a 10-bike pool and a versioned seat map")
expect(booking_create_resource(store, sa, t, admin, "bikes", "capacity-pool", 10, "").reason).to_equal("accepted")
expect(booking_create_resource(store, sa, t, admin, "hall", "assigned-seat", 0, "v1").reason).to_equal("accepted")

step("Pool: hold 6 bikes, confirm, then a no-show is recorded")
expect(booking_hold(store, ags, t, agent, envelope("p-h1", "booking.hold"), "pool-1", "bikes", t0(), t0() + 100, 6, "", t0(), 300).reason).to_equal("accepted")
expect(booking_confirm(store, ags, t, agent, envelope("p-c1", "booking.confirm"), "pool-1", t0()).reason).to_equal("accepted")
expect(booking_no_show(store, ags, t, agent, envelope("p-n1", "booking.no_show"), "pool-1").reason).to_equal("accepted")
expect(booking_status(store, "tenant-a", "pool-1")).to_equal("no-show")

step("Seat: hold seat A1, confirm, cancel")
expect(booking_hold(store, ags, t, agent, envelope("s-h1", "booking.hold"), "seat-1", "hall", t0(), t0() + 100, 1, "A1", t0(), 300).reason).to_equal("accepted")
expect(booking_confirm(store, ags, t, agent, envelope("s-c1", "booking.confirm"), "seat-1", t0()).reason).to_equal("accepted")
expect(booking_cancel(store, ags, t, agent, envelope("s-x1", "booking.cancel"), "seat-1").reason).to_equal("accepted")
expect(booking_status(store, "tenant-a", "seat-1")).to_equal("cancelled")
store_close(store)
```

</details>

### booking vertical — overlap policy rejects conflicts per mode

#### rejects an exclusive double-book, a pool over-capacity, and a taken seat

- Exclusive: a confirmed booking blocks any overlapping hold
   - Expected: d1.reason equals `conflict`
- Exclusive: an adjacent (non-overlapping) range is fine
   - Expected: booking_hold(store, ags, t, agent, envelope("c-e4", "booking.hold"), "ex-3", "cabin-1", t0() + 200, t0() + 300, 1, "", t0(), 300).reason equals `accepted`
- Pool: 6 + 5 exceeds capacity 10; 6 + 4 fits exactly
   - Expected: d2.reason equals `conflict`
   - Expected: booking_hold(store, ags, t, agent, envelope("c-p3", "booking.hold"), "pl-3", "bikes", t0() + 50, t0() + 150, 4, "", t0(), 300).reason equals `accepted`
- Seat: A1 taken in an overlapping session; B1 is free
   - Expected: d3.reason equals `conflict`
   - Expected: booking_hold(store, ags, t, agent, envelope("c-s3", "booking.hold"), "st-3", "hall", t0() + 10, t0() + 90, 1, "B1", t0(), 300).reason equals `accepted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("conflicts")
val t = tenant_a()
val admin = admin_a()
val sa = session_for(admin, t)
val agent = agent_a()
val ags = session_for(agent, t)
booking_create_resource(store, sa, t, admin, "cabin-1", "exclusive-unit", 0, "")
booking_create_resource(store, sa, t, admin, "bikes", "capacity-pool", 10, "")
booking_create_resource(store, sa, t, admin, "hall", "assigned-seat", 0, "v1")

step("Exclusive: a confirmed booking blocks any overlapping hold")
booking_hold(store, ags, t, agent, envelope("c-e1", "booking.hold"), "ex-1", "cabin-1", t0() + 100, t0() + 200, 1, "", t0(), 300)
booking_confirm(store, ags, t, agent, envelope("c-e2", "booking.confirm"), "ex-1", t0())
val d1 = booking_hold(store, ags, t, agent, envelope("c-e3", "booking.hold"), "ex-2", "cabin-1", t0() + 150, t0() + 250, 1, "", t0(), 300)
expect(d1.ok).to_be(false)
expect(d1.reason).to_equal("conflict")
step("Exclusive: an adjacent (non-overlapping) range is fine")
expect(booking_hold(store, ags, t, agent, envelope("c-e4", "booking.hold"), "ex-3", "cabin-1", t0() + 200, t0() + 300, 1, "", t0(), 300).reason).to_equal("accepted")

step("Pool: 6 + 5 exceeds capacity 10; 6 + 4 fits exactly")
booking_hold(store, ags, t, agent, envelope("c-p1", "booking.hold"), "pl-1", "bikes", t0(), t0() + 100, 6, "", t0(), 300)
val d2 = booking_hold(store, ags, t, agent, envelope("c-p2", "booking.hold"), "pl-2", "bikes", t0() + 50, t0() + 150, 5, "", t0(), 300)
expect(d2.reason).to_equal("conflict")
expect(booking_hold(store, ags, t, agent, envelope("c-p3", "booking.hold"), "pl-3", "bikes", t0() + 50, t0() + 150, 4, "", t0(), 300).reason).to_equal("accepted")

step("Seat: A1 taken in an overlapping session; B1 is free")
booking_hold(store, ags, t, agent, envelope("c-s1", "booking.hold"), "st-1", "hall", t0(), t0() + 100, 1, "A1", t0(), 300)
val d3 = booking_hold(store, ags, t, agent, envelope("c-s2", "booking.hold"), "st-2", "hall", t0() + 10, t0() + 90, 1, "A1", t0(), 300)
expect(d3.reason).to_equal("conflict")
expect(booking_hold(store, ags, t, agent, envelope("c-s3", "booking.hold"), "st-3", "hall", t0() + 10, t0() + 90, 1, "B1", t0(), 300).reason).to_equal("accepted")
store_close(store)
```

</details>

### booking vertical — expired holds release the slot

#### an expired hold no longer blocks, and cannot be confirmed

- Hold with a 300s TTL at t0
   - Expected: booking_hold(store, ags, t, agent, envelope("x-h1", "booking.hold"), "bk-1", "cabin-1", t0() + 100, t0() + 200, 1, "", t0(), 300).reason equals `accepted`
- Before expiry the slot is blocked
   - Expected: booking_hold(store, ags, t, agent, envelope("x-h2", "booking.hold"), "bk-2", "cabin-1", t0() + 100, t0() + 200, 1, "", t0() + 100, 300).reason equals `conflict`
- After expiry (now = t0+301) a new hold succeeds
   - Expected: booking_hold(store, ags, t, agent, envelope("x-h3", "booking.hold"), "bk-3", "cabin-1", t0() + 100, t0() + 200, 1, "", t0() + 301, 300).reason equals `accepted`
- The expired hold can no longer be confirmed
   - Expected: c.reason equals `invalid-record`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("expiry")
val t = tenant_a()
val admin = admin_a()
val sa = session_for(admin, t)
val agent = agent_a()
val ags = session_for(agent, t)
booking_create_resource(store, sa, t, admin, "cabin-1", "exclusive-unit", 0, "")

step("Hold with a 300s TTL at t0")
expect(booking_hold(store, ags, t, agent, envelope("x-h1", "booking.hold"), "bk-1", "cabin-1", t0() + 100, t0() + 200, 1, "", t0(), 300).reason).to_equal("accepted")

step("Before expiry the slot is blocked")
expect(booking_hold(store, ags, t, agent, envelope("x-h2", "booking.hold"), "bk-2", "cabin-1", t0() + 100, t0() + 200, 1, "", t0() + 100, 300).reason).to_equal("conflict")

step("After expiry (now = t0+301) a new hold succeeds")
expect(booking_hold(store, ags, t, agent, envelope("x-h3", "booking.hold"), "bk-3", "cabin-1", t0() + 100, t0() + 200, 1, "", t0() + 301, 300).reason).to_equal("accepted")

step("The expired hold can no longer be confirmed")
val c = booking_confirm(store, ags, t, agent, envelope("x-c1", "booking.confirm"), "bk-1", t0() + 301)
expect(c.ok).to_be(false)
expect(c.reason).to_equal("invalid-record")
store_close(store)
```

</details>

### booking vertical — guarded sequence denies at every rung

#### rejects bad sessions, roles, resources, and ranges

- Inactive session
   - Expected: booking_hold(store, dead, t, agent, envelope("g-1", "booking.hold"), "bk-1", "cabin-1", t0(), t0() + 100, 1, "", t0(), 300).reason equals `invalid-session`
- Viewer role forbidden
   - Expected: booking_hold(store, session_for(viewer, t), t, viewer, envelope("g-2", "booking.hold"), "bk-1", "cabin-1", t0(), t0() + 100, 1, "", t0(), 300).reason equals `forbidden`
- Unknown resource
   - Expected: booking_hold(store, ags, t, agent, envelope("g-3", "booking.hold"), "bk-1", "ghost", t0(), t0() + 100, 1, "", t0(), 300).reason equals `not-found`
- Inverted time range
   - Expected: booking_hold(store, ags, t, agent, envelope("g-4", "booking.hold"), "bk-1", "cabin-1", t0() + 100, t0(), 1, "", t0(), 300).reason equals `invalid-record`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("guards")
val t = tenant_a()
val agent = agent_a()
step("Inactive session")
var dead = session_for(agent, t)
dead.active = false
expect(booking_hold(store, dead, t, agent, envelope("g-1", "booking.hold"), "bk-1", "cabin-1", t0(), t0() + 100, 1, "", t0(), 300).reason).to_equal("invalid-session")
step("Viewer role forbidden")
val viewer = viewer_a()
expect(booking_hold(store, session_for(viewer, t), t, viewer, envelope("g-2", "booking.hold"), "bk-1", "cabin-1", t0(), t0() + 100, 1, "", t0(), 300).reason).to_equal("forbidden")
step("Unknown resource")
val ags = session_for(agent, t)
expect(booking_hold(store, ags, t, agent, envelope("g-3", "booking.hold"), "bk-1", "ghost", t0(), t0() + 100, 1, "", t0(), 300).reason).to_equal("not-found")
step("Inverted time range")
val admin = admin_a()
booking_create_resource(store, session_for(admin, t), t, admin, "cabin-1", "exclusive-unit", 0, "")
expect(booking_hold(store, ags, t, agent, envelope("g-4", "booking.hold"), "bk-1", "cabin-1", t0() + 100, t0(), 1, "", t0(), 300).reason).to_equal("invalid-record")
store_close(store)
```

</details>

### booking vertical — idempotent replay produces exactly one effect

#### replaying the same hold command changes nothing

- Hold once
   - Expected: first.reason equals `accepted`
- Replay the SAME idempotency key
   - Expected: replay.reason equals `duplicate-key`
   - Expected: replay.detail equals `bk-1`
- No second effect — outbox unchanged, pool sees one 4-unit hold
   - Expected: outbox_pending(store, "tenant-a").len() equals `outbox_after_first`
   - Expected: booking_hold(store, ags, t, agent, envelope("other-key", "booking.hold"), "bk-2", "bikes", t0(), t0() + 100, 6, "", t0(), 300).reason equals `accepted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("replay")
val t = tenant_a()
val admin = admin_a()
booking_create_resource(store, session_for(admin, t), t, admin, "bikes", "capacity-pool", 10, "")
val agent = agent_a()
val ags = session_for(agent, t)

step("Hold once")
val first = booking_hold(store, ags, t, agent, envelope("same-key", "booking.hold"), "bk-1", "bikes", t0(), t0() + 100, 4, "", t0(), 300)
expect(first.reason).to_equal("accepted")
val outbox_after_first = outbox_pending(store, "tenant-a").len()

step("Replay the SAME idempotency key")
val replay = booking_hold(store, ags, t, agent, envelope("same-key", "booking.hold"), "bk-1", "bikes", t0(), t0() + 100, 4, "", t0(), 300)
expect(replay.ok).to_be(true)
expect(replay.reason).to_equal("duplicate-key")
expect(replay.detail).to_equal("bk-1")

step("No second effect — outbox unchanged, pool sees one 4-unit hold")
expect(outbox_pending(store, "tenant-a").len()).to_equal(outbox_after_first)
# If the replay had double-counted, 7 more would exceed capacity 10.
expect(booking_hold(store, ags, t, agent, envelope("other-key", "booking.hold"), "bk-2", "bikes", t0(), t0() + 100, 6, "", t0(), 300).reason).to_equal("accepted")
store_close(store)
```

</details>

### booking vertical — tenant isolation

#### tenant B neither sees nor collides with tenant A's resources

- Tenant B cannot hold tenant A's resource (not visible)
   - Expected: booking_hold(store, sb, tb, agent_b, envelope("i-2", "booking.hold"), "bk-b", "cabin-1", t0(), t0() + 100, 1, "", t0(), 300).reason equals `not-found`
- A cross-tenant session is rejected outright
   - Expected: booking_hold(store, sb, ta, agent_b, envelope("i-3", "booking.hold"), "bk-b2", "cabin-1", t0(), t0() + 100, 1, "", t0(), 300).reason equals `invalid-session`
- Tenant A's booking is untouched
   - Expected: booking_status(store, "tenant-a", "bk-a") equals `hold`
   - Expected: booking_status(store, "tenant-b", "bk-a") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("isolation")
val ta = tenant_a()
val admin = admin_a()
booking_create_resource(store, session_for(admin, ta), ta, admin, "cabin-1", "exclusive-unit", 0, "")
val agent = agent_a()
val ags = session_for(agent, ta)
booking_hold(store, ags, ta, agent, envelope("i-1", "booking.hold"), "bk-a", "cabin-1", t0(), t0() + 100, 1, "", t0(), 300)

step("Tenant B cannot hold tenant A's resource (not visible)")
val tb = tenant_b()
val agent_b = ActorContext(actor_id: "agent-b", role: "booking")
val sb = session_for(agent_b, tb)
expect(booking_hold(store, sb, tb, agent_b, envelope("i-2", "booking.hold"), "bk-b", "cabin-1", t0(), t0() + 100, 1, "", t0(), 300).reason).to_equal("not-found")

step("A cross-tenant session is rejected outright")
expect(booking_hold(store, sb, ta, agent_b, envelope("i-3", "booking.hold"), "bk-b2", "cabin-1", t0(), t0() + 100, 1, "", t0(), 300).reason).to_equal("invalid-session")

step("Tenant A's booking is untouched")
expect(booking_status(store, "tenant-a", "bk-a")).to_equal("hold")
expect(booking_status(store, "tenant-b", "bk-a")).to_equal("")
store_close(store)
```

</details>

### booking vertical — state survives restart

#### reopens the database with bookings and the replay guard intact

- Close the store (simulated shutdown)
- Reopen and verify status, conflict policy, audit, replay guard
   - Expected: booking_status(store2, "tenant-a", "bk-1") equals `confirmed`
   - Expected: booking_hold(store2, ags, t, agent, envelope("r-h2", "booking.hold"), "bk-2", "cabin-1", t0() + 150, t0() + 250, 1, "", t0(), 300).reason equals `conflict`
   - Expected: replay.reason equals `duplicate-key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = fresh_store("restart")
val t = tenant_a()
val admin = admin_a()
booking_create_resource(store, session_for(admin, t), t, admin, "cabin-1", "exclusive-unit", 0, "")
val agent = agent_a()
val ags = session_for(agent, t)
booking_hold(store, ags, t, agent, envelope("r-h1", "booking.hold"), "bk-1", "cabin-1", t0() + 100, t0() + 200, 1, "", t0(), 300)
booking_confirm(store, ags, t, agent, envelope("r-c1", "booking.confirm"), "bk-1", t0())
step("Close the store (simulated shutdown)")
store_close(store)

step("Reopen and verify status, conflict policy, audit, replay guard")
val store2 = store_open(db_path("restart"))
expect(store2.open_ok).to_be(true)
expect(booking_status(store2, "tenant-a", "bk-1")).to_equal("confirmed")
expect(booking_hold(store2, ags, t, agent, envelope("r-h2", "booking.hold"), "bk-2", "cabin-1", t0() + 150, t0() + 250, 1, "", t0(), 300).reason).to_equal("conflict")
expect(audit_verify_chain(store2, "tenant-a")).to_be(true)
val replay = booking_hold(store2, ags, t, agent, envelope("r-h1", "booking.hold"), "bk-1", "cabin-1", t0() + 100, t0() + 200, 1, "", t0(), 300)
expect(replay.reason).to_equal("duplicate-key")
store_close(store2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
