# Enterprise Assets — fixed-asset register and straight-line depreciation

The assets vertical of the Simple Enterprise Suite. It registers fixed assets,
folds capitalized improvements into their basis, posts a straight-line
depreciation schedule period by period, and retires them with a realised gain or
loss — all over the durable enterprise store, with exact integer minor-unit
arithmetic and no floats anywhere in the pipeline.

- Module: `src/lib/nogc_sync_mut/enterprise_assets/assets.spl`
- Spec: `test/01_unit/lib/nogc_sync_mut/enterprise_assets_spec.spl`
- Probe: `src/app/enterprise/assets_probe_main.spl`

## Storage model

Two insert-only tables, created by `assets_setup`:

| Table | Columns | Role |
|-------|---------|------|
| `asset_register` | `tenant_id, asset_id, cost_cents, salvage_cents, life_periods, acquired_by` | one acquisition row per asset |
| `asset_events` | `tenant_id, asset_id, event, amount_cents, period` | append-only `capitalize` / `post` / `dispose` journal |

Nothing is ever UPDATEd or DELETEd. Every derived quantity — basis, schedule,
accumulated depreciation, book value, disposed-ness — is a pure fold over these
rows, and every fold filters on `tenant_id`, so tenant B can never observe
tenant A's assets even when both use the same `asset_id`.

## Straight-line schedule

`assets_schedule` spreads `basis - salvage` over `life_periods` equal periods
using integer division, with the truncation remainder absorbed by the **final**
period:

```
per_period = (basis - salvage) / life_periods
last       = (basis - salvage) - per_period * (life_periods - 1)
```

This is the whole reason the vertical is float-free: the schedule reconciles to
`basis - salvage` **exactly**, with no drift to sweep up at year end.

| basis | salvage | life | schedule | sum |
|-------|---------|------|----------|-----|
| 10000 | 1000 | 3 | 3000, 3000, 3000 | 9000 |
| 10000 | 0 | 3 | 3333, 3333, **3334** | 10000 |
| 12000 | 1000 | 3 | 3666, 3666, **3668** | 11000 |

The third row is the capitalization case: capitalizing 2000 onto a
10000/1000/3 asset moves the basis to 12000 and reshapes the schedule; the
acquisition row is never rewritten.

## Commands

All four run the **frozen** guarded sequence — session -> rbac -> validation ->
idempotency -> effects, with every effect inside one unit of work — and chain a
sha256 audit record through the `records.audit_append` facade.

| Command | Effect | Rejects (`invalid-record`) |
|---------|--------|----------------------------|
| `assets_acquire` | registers a new asset | empty id, cost <= 0, salvage < 0 or > cost, **life <= 0**, duplicate id |
| `assets_capitalize` | appends an improvement to the basis | amount <= 0, unknown asset, disposed asset |
| `assets_post_period` | posts one period's scheduled depreciation | unknown asset, period outside `1..life`, **period already posted**, disposed asset |
| `assets_dispose` | retires the asset for proceeds | negative proceeds, unknown asset, **already disposed** |

Posting is bounded by `life_periods` and each period can be posted once, so an
asset can never depreciate past its salvage floor: posting all three periods of
a 10000/1000/3 asset leaves the book value at exactly 1000.

## Disposal gain / loss

`assets_gain_loss(store, tenant, asset, proceeds) = proceeds - book_value`,
where `book_value = basis - accumulated`. Positive is a gain, negative a loss,
zero break-even. A **second** disposal is rejected by folding the existing
`dispose` rows — not by a mutable flag — and a disposed asset can no longer be
capitalized or depreciated.

## RBAC

Asset commands reuse the existing **`finance`** role through the local
`assets_role_allows` gate (`admin` passes for everything, matching the frozen
blanket rule). The frozen `role_allows` table and
`enterprise_sale/rbac_registry.spl` are deliberately **not** edited — the
registry's equivalence spec is byte-fenced to the frozen table, so adding a
grant there would turn it red.

## Running the spec

```bash
sh scripts/resource/test-slot.shs bin/simple test \
  test/01_unit/lib/nogc_sync_mut/enterprise_assets_spec.spl --timeout 800
```

Lane: `.spipe/simple_enterprise_suite` (W23-FAN, assets).
