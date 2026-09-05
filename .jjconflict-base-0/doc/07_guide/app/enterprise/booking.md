# Enterprise Booking — booking/rental vertical (std.enterprise_booking)

The booking/rental proving vertical of the Simple Enterprise Suite
(assessment §7.2, Wave 3, ReservableResource model). Builds only on
`std.enterprise_store` (durable UoW / idempotency / outbox / audit) and
`std.enterprise_sale.foundation` (contexts, envelope, guarded sequence).

Module: `src/lib/nogc_sync_mut/enterprise_booking/booking.spl`
(`use std.enterprise_booking` resolves via the async-tier wrapper,
mirroring `std.enterprise_sale`).

## Resource model

`booking_create_resource(store, session, tenant, who, resource_id, mode,
capacity, seat_map_version)` — admin-guarded. Modes:

| Mode | Overlap policy |
|------|----------------|
| `exclusive-unit` | no overlapping active booking at all |
| `capacity-pool` | sum of overlapping active quantities <= capacity |
| `assigned-seat` | seat id free in every overlapping session (`seat_map_version` recorded) |

"Active" = confirmed booking OR non-expired hold. Expired holds never
block. All expiry judgements use the CALLER-SUPPLIED `now_epoch` — the
library performs no wall-clock reads, so behaviour is deterministic and
server time is the single authority.

## Commands (frozen guarded sequence)

Every command runs: session -> rbac -> validation -> idempotency ->
effects in one UoW (event row + outbox + audit + idempotency key), exactly
like `goods_sale`.

- `booking_hold(..., booking_id, resource_id, start_epoch, end_epoch, qty, seat, now_epoch, ttl_seconds)`
  — places a hold expiring at `now_epoch + ttl_seconds`; conflict policy enforced.
- `booking_confirm(..., booking_id, now_epoch)` — hold -> confirmed; an
  expired hold is `invalid-record`; conflicts re-checked excluding self.
- `booking_cancel(..., booking_id)` — hold/confirmed -> cancelled.
- `booking_no_show(..., booking_id)` — confirmed -> no-show.

Reads: `booking_resource_mode`, `booking_status` (event-stream derived:
hold -> confirmed -> cancelled | no-show), `booking_conflicts`.

## Denial reasons

The frozen closed set from `enterprise_sale/foundation.spl`:
`invalid-session | forbidden | invalid-record | not-found | duplicate-key |
conflict`. `conflict` is the one reason added for this vertical (a valid
command colliding with an active reservation). RBAC: role `booking` may
hold/confirm/cancel/no_show; `admin` may everything incl. resource create.

## Storage

Insert-only + derive (interpreter-sqlite compatible): `booking_resources`
plus `booking_events`, where the `hold` row carries range/qty/seat/expiry
and later events only advance status. One sqlite db path per scenario.

## Spec

`test/03_system/app/enterprise/booking_vertical_spec.spl` — 8 examples:
per-mode lifecycle, per-mode conflict rejection, expired-hold release,
guard rungs, idempotent replay (exactly one effect), tenant isolation,
restart survival. Doc: `doc/06_spec/...` (spipe_docgen).
