# Enterprise Warehouse — bins, putaway, FEFO/FIFO picking, pack

Lane: `.spipe/simple_enterprise_suite` (W23-FAN, warehouse).

- Module: `src/lib/nogc_sync_mut/enterprise_warehouse/warehouse.spl`
- Spec: `test/01_unit/lib/nogc_sync_mut/enterprise_warehouse_spec.spl` (8 examples)
- Probe: `src/app/enterprise/warehouse_probe_main.spl`

## Scope — and what this vertical deliberately does NOT own

This module owns **bin-level topology**: where stock physically sits and how it
moves in and out of a bin. Aggregate on-hand quantity is `enterprise_inventory`
and inter-site movement is `enterprise_transfer`; neither is imported, extended,
or edited here. The warehouse layer sits *below* inventory quantities and is
standalone, so it can be reasoned about (and tested) without either.

`enterprise_sale/foundation.spl` and `enterprise_sale/rbac_registry.spl` are
FROZEN and untouched.

## Storage model — insert-only, no UPDATE anywhere

| Table | Row meaning |
|-------|-------------|
| `wh_bins (tenant_id, bin_code, zone, capacity, set_by)` | bin registration; re-registering appends and the LATEST row wins |
| `wh_putaway (tenant_id, bin_code, sku, qty, lot, expiry_day, put_by)` | one putaway |
| `wh_picked (tenant_id, bin_code, sku, qty, lot, order_id)` | one confirmed pack line |

Occupancy is never stored — it is the pure fold `sum(putaway) - sum(picked)`
(`wh_bin_used`). A bin is UNKNOWN until registered: `wh_bin_capacity` returns
`-1`, and `wh_bin_free` returns `-1` rather than a misleading `0`.

## Capacity rule

Putaway of `qty` is accepted iff `used(bin) + qty <= capacity(bin)`. The boundary
is **inclusive** — exactly filling a bin is accepted; the spec asserts both sides
of it (8+2 into a capacity-10 bin passes; 8+3 does not). Because the check reads
the current fold, a pack frees capacity for a later putaway.

## Pick ordering — FEFO, FIFO on a tie

`wh_pick_list` sorts candidate lots by `(expiry_day, row_id)` ascending:
First-Expired-First-Out, with the earliest putaway winning an expiry tie. `row_id`
is unique, so the order is **total** and the plan is reproducible run to run.

The spec proves the two halves separately and in a way insert order cannot
explain: the FEFO case puts the LATE-expiring lot away FIRST and still expects the
EARLY lot picked first; the FIFO case uses two lots with identical expiry.

`expiry_day` is an integer day number (e.g. `20260901` as yyyymmdd). Integers keep
the ordering total and float-free. `0` means "no expiry" and sorts FIRST — pass a
large sentinel instead if no-expiry stock should be picked LAST.

## Short picks are a normal outcome

When stock is insufficient, `wh_pick_list` returns every line it could allocate
plus `short_qty > 0` and `complete: false`. It is never an error and never
partially fails — the caller decides whether to pack a short line.

## Denial reasons map onto the FROZEN closed set

`foundation.reason_set()` is byte-fenced by a conformance spec and widening it
requires an ADR, so this module does **not** invent `unknown-bin` or `bin-full`.
The two warehouse-specific conditions map onto existing members:

| Condition | Reason returned |
|-----------|-----------------|
| bin never registered for this tenant | `not-found` |
| putaway would exceed capacity | `conflict` |
| packing more than the bin holds | `insufficient-stock` |
| non-ops, non-admin actor | `forbidden` |
| replayed idempotency key | `duplicate-key` |

The `detail` string still carries `bin/sku/lot:qty`, so the specific condition
stays machine-readable downstream. Every reason the spec asserts is additionally
run through `reason_allowed`, so introducing a fresh reason string turns the spec
red — that is the enforcement, not this prose.

## RBAC

All three commands reuse the existing `ops` role through the LOCAL
`wh_role_allows` gate (`admin` passes everything, matching the frozen blanket
rule). `rbac_registry.spl` is deliberately not touched — its equivalence spec is
fenced to the frozen table, so adding a grant there would turn it red.

## Guarded sequence

Every write runs session -> rbac -> validation -> idempotency -> effects in one
UoW, with `outbox_append` / `audit_append` / `idempotency_record` inside the
transaction. State-dependent validation (unknown bin, capacity, stock) runs after
the static validation rung and **before** idempotency, so a replayed key never
re-evaluates state. Audit hashing goes only through the `records.audit_append`
facade; this module never imports `std.common.crypto.sha256`.

## Known grammar defect hit while writing this

Writing the FEFO comparison inline as

```
pool[i].expiry_day < pool[best].expiry_day
```

makes the parser read `< pool[...] >` as a generic argument list and emit
`warning: Deprecated syntax for type parameters ... Use angle brackets:
pool<...>`. The code still evaluates correctly (the spec passed with the warning
present), so this is a diagnostic-only defect, but it is a real ambiguity in a
short, natural expression form: an indexed field compared with `<` against
another indexed expression. Worked around by binding both comparands to locals
first; the workaround is commented at the call site rather than silently
normalised. Reproduce with any `a[i].f < a[j].f` on an array of structs.
