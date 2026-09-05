# Replay and state-dependent validation (canonical rule)

This is the single, canonical statement of the rule for every vertical in
the Simple Enterprise Suite. Per-vertical manuals link here rather than
restating it.

## The frozen guarded sequence

Every write runs the same rungs, in this order, and the order does not move:

    session -> rbac -> domain validation -> idempotency -> effects in one UoW

## The rule

> **Feasibility is a question about a command that has NOT yet been
> recorded.**

A validation check is *state-dependent* when it reads state that this very
command changes on its first execution — available stock, remaining
quantity, uninvoiced amount, or a status the command itself advances.
Evaluating such a check on a replay re-judges an outcome that was already
decided and accepted, so the replay is denied a domain reason instead of
returning the recorded result.

The fix is not to reorder the rungs. It is to ask the state-dependent
question only of a command that `idempotency_seen` says is not already
recorded:

```
val replayed = idempotency_seen(store, tenant_id, envelope.idempotency_key)
if not replayed and <state-dependent check fails>:
    return denied("<domain reason>", detail)
if replayed:
    return CommandResult(ok: true, reason: "duplicate-key", detail: ...)
```

## What stays unconditional

State-**independent** identity and shape checks are unaffected and remain
unconditional, ahead of the idempotency probe:

- empty or malformed ids, non-positive quantities and amounts
  (`invalid-record`);
- an entity that does not exist and that this command never creates —
  unknown SKU, unknown PO, unknown order (`not-found` / `invalid-record`).

A replay of a command against a nonexistent entity is still a denial: the
command could not have been accepted in the first place.

## Consequences to keep true

- A replay with the same idempotency key returns `ok=true`,
  `reason="duplicate-key"`, `detail` = the recorded result, and produces no
  second effect (stock, outbox, and journal all unchanged).
- A **fresh** key for the same now-infeasible command is still denied with
  the domain reason. Making replay work must not disable the guard.

## Where this applies today

| Vertical | Command | State-dependent check made replay-aware |
|----------|---------|------------------------------------------|
| procurement | `proc_receive` | over-receipt vs remaining (`insufficient-stock`) |
| procurement | `proc_invoice_record` | invoice beyond received (`invalid-record`) |
| goods sale | `sale_place_order` | available stock vs qty (`insufficient-stock`) |
| goods sale | `sale_pay_order` | `created -> paid` transition (`invalid-record`) |
| goods sale | `sale_refund_order` | `paid -> refunded` transition (`invalid-record`) |

Any new command whose validation reads its own effect needs the same
treatment, and a spec example that replays it after the effect has made it
infeasible.

## History

Found by lane W6-B during the procurement green run: replaying a receipt was
denied `insufficient-stock` instead of returning `duplicate-key`. Lane W7-A
reproduced the identical shape in `std.enterprise_sale` — a replayed order
that had consumed the last of the stock, and replayed pay/refund whose own
effect had advanced the order status — and closed it the same way. Covered by
`test/03_system/app/enterprise/goods_sale_vertical_spec.spl` ("a replay of a
self-infeasible command still replays") and the procurement replay examples.
