# Enterprise Restaurant — table-service vertical (`std.enterprise_restaurant`)

The table-service proving vertical of the Simple Enterprise Suite (lane
`.spipe/simple_enterprise_suite`, W2-E). It builds ONLY on
`std.enterprise_store` (durable UoW / idempotency / outbox / audit) and
`std.enterprise_sale.foundation` (contexts, `CommandEnvelope`/`CommandResult`,
the frozen guarded sequence), and reuses the sale catalog as its menu: a menu
item IS a `products` row — a line references a product `sku` and snapshots
its price (`sale_product_price`) at line time. There is no second product
table.

Implementation: `src/lib/nogc_sync_mut/enterprise_restaurant/restaurant.spl`
(default-tier wrapper: `src/lib/nogc_async_mut/enterprise_restaurant/__init__.spl`).
Spec: `test/03_system/app/enterprise/restaurant_vertical_spec.spl`
(doc: `doc/06_spec/03_system/app/enterprise/restaurant_vertical_spec.md`).

## Flow

```
restaurant_setup(store)                      # applies sale schema + restaurant tables
table_open_session(...)                      # one ACTIVE session per (venue, table)
order_add_line(...)                          # menu sku + qty + free-text modifiers,
                                             # price snapshotted from the sale catalog
kitchen_mark_ready(...)                      # ordered -> ready   (forward-only)
line_mark_served(...)                        # ready   -> served
order_void_line(...)                         # ordered|ready -> voided (bills nothing)
bill_close_session(...)                      # totals SERVED lines, posts balanced
                                             # cash/sales_revenue pair, closes session
```

Every command runs the frozen guarded sequence
`session -> rbac -> validation -> idempotency -> effects in one UoW`, with
the outbox event, audit record, and idempotency key committed in the same
unit of work as the domain event. Storage is insert-only event streams
(`rest_session_events`, `rest_line_events`); all state is derived in pure
Simple (interpreter-backend safe — no UPDATE/WHERE).

## Frozen denial reasons (beyond the foundation's closed set)

| Reason | Fires when |
|--------|-----------|
| `table-occupied` | opening a table that already has an active session |
| `no-session` | adding a line / closing a bill for an unknown session |
| `session-closed` | adding a line to (or re-closing) a closed session |
| `invalid-transition` | any non-forward line transition (e.g. serve before ready) |
| `unserved-lines` | closing while a line is still ordered/ready (void it instead) |
| `line-not-found` | transitioning a line that was never ordered |

## Reads

`restaurant_table_session` (active session per table),
`restaurant_session_state` (`opened`/`closed`), `restaurant_line_status`,
`restaurant_session_lines`, `restaurant_session_total` (served lines only).
Journal balance oracle stays `sale_journal_balanced`.
