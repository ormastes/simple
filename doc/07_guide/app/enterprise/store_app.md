# Enterprise Store App

Customer-facing store vertical of the Simple Enterprise Suite
(`.spipe/simple_enterprise_suite`, Goal Set v2 AC-15/AC-16).

Module: `src/app/enterprise_store_app/main.spl`

## What it is

A pure-Simple HTTP-shaped dispatcher (`store_app_handle`) that carries a
customer from catalog to receipt, built ONLY on existing layers:

- **Storage / commands**: `std.enterprise_store` (WAL sqlite, UoW,
  idempotency, outbox, audit chain) + `std.enterprise_sale`
  (`sale_place_order` / `sale_pay_order` — the frozen guarded sequence:
  session -> rbac -> validation -> idempotency -> effects in one UoW).
- **Route hardening**: `std.common.net.http_core` — `body_decision`
  (limits, smuggling rejection), `path_is_safe` (traversal),
  `match_route_pattern` / `extract_route_params` (routing).
- **Responses**: `std.nogc_sync_mut.http_server` `HttpResponse` +
  the shared `with_default_security_headers` policy (never duplicated).

## Routes

| Method | Path | Action |
|--------|------|--------|
| GET | `/store/catalog` | Escaped HTML catalog for the session's tenant |
| POST | `/store/order` | body `order=O&sku=S&qty=N&idem=K` -> `sale_place_order` |
| POST | `/store/pay` | body `order=O&idem=K` -> `sale_pay_order` |
| GET | `/store/order/:id/receipt` | Escaped HTML receipt (status derived) |

Dispatch order for every request: limits -> path safety -> authenticated
session (`session_valid`, the only auth scheme) -> route. Denial mapping:
invalid-session 401, forbidden 403, not-found 404, stock/record conflicts
409; idempotent replay returns 200 with the recorded `duplicate-key` result.

All interpolated business data passes through `esc()` — a product named
`<script>...</script>` renders as `&lt;script&gt;...`.

The cart (`cart_new` / `cart_add` / `cart_total_cents`) is a pure
request-scoped model; checkout (the POST) is the only effect.

## Specs

- `test/03_system/app/enterprise/store_app_spec.spl` — end-to-end flow,
  idempotent replay (exactly one effect), tenant isolation (AC-16).
- `test/03_system/app/enterprise/store_web_harden_spec.spl` —
  unauthenticated denial, HTML escaping, shared security headers,
  http_core limit/traversal gating (AC-15).

Run one at a time: `bin/simple test <spec>` (interpreter-mode evidence;
per-scenario db paths because the interpreter caches sqlite per path).
