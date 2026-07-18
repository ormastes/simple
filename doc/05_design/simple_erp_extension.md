# Simple ERP — Extensible Business Framework Design

## Research: how the incumbents extend

- **Odoo**: a business is a *module* (models + views + security records) loaded
  into a registry; the framework derives menus, ACLs, and routes from module
  manifests, never from framework edits.
- **SAP**: business configuration lives in customizing tables + registered
  extensions (BAdIs); core code stays untouched per installation.
- Common core: **registration over modification** — one descriptor per business,
  everything else derived.

## Design: LaneDef registry (the one extension point)

`src/framework/registry.spl` defines:

```
struct LaneDef: name, write_action, write_path, threshold_minor, approver_role
fn lane_def(name, write_path, threshold_minor, approver_role) -> LaneDef
fn default_lanes() -> [LaneDef]        # the stock 5-lane suite
fn is_registered_write(lanes, action) -> bool
```

Everything a business needs is DERIVED from `lanes: [LaneDef]`:

| Concern | Derivation |
|---|---|
| RBAC | `role_can_for(lanes, role, action)` — operator may write exactly the registered actions; unregistered actions are forbidden (fail-closed) |
| Gate | `gate_write_for(lanes, ...)` — session → RBAC → validation → idempotency (+ `gate_write_with_approval` overlay) |
| Routes | `routes_for(lanes)` — one POST write route per lane + fixed read surfaces; `dispatch_for(lanes, ...)` |
| Reporting/look | `LaneKpi` per lane; `render_dashboard` is registry-agnostic |

The un-suffixed functions (`role_can`, `gate_write`, `route_table`, `dispatch`)
are thin delegates bound to `default_lanes()` so the stock suite and its specs
stay unchanged.

## Adding a new business (the whole recipe)

1. Write one lane module (domain structs + validation + transitions + a
   `submit_*_write` that calls `gate_write_for` with its action).
2. Register it: `lanes.push(lane_def("clinic", "/api/clinic/appointments", 200000, "admin"))`.
3. Done — RBAC, routing, gating, KPI cards all pick it up.

Executable proof: `src/extension_demo.spl` adds a clinic lane (6th business)
with zero framework edits and prints `framework-edits=0`. Pinned by
`ubs_test/registry_spec.spl` (registered write allowed, unregistered
forbidden, route derived, default table unchanged).

## Refactor notes

- The previously enumerated operator policy moved from `role_can` into the
  registry derivation — the enumeration is now *data* the app owns.
- `route_table()` was hardcoded; now derived. No route behavior changed for
  the stock suite (spec-verified: 7 routes, same paths).
- Approval thresholds live on `LaneDef` so per-business policy is
  registration data too.
