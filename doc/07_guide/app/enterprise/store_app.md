# Enterprise Store App

Customer-facing store vertical of the Simple Enterprise Suite
(`.spipe/simple_enterprise_suite`, Goal Set v2 AC-15/AC-16).

Modules: `src/app/enterprise_store_app/main.spl` (dispatcher + store routes),
`web_common.spl` (esc/form parsing/security wrapper/denial mapping),
`booking_routes.spl`, `restaurant_routes.spl`, `dashboard.spl` (W3-B route
families, all dispatched through the same hardened prelude in `main.spl`).

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
| GET | `/booking/resources` | Escaped list of the tenant's reservable resources |
| POST | `/booking/hold` | body `booking=B&resource=R&start=E&end=E&qty=N&seat=S&now=E&ttl=N&idem=K` -> `booking_hold` (epochs/ttl digit-checked) |
| POST | `/booking/confirm` | body `booking=B&now=E&idem=K` -> `booking_confirm` |
| POST | `/booking/cancel` | body `booking=B&idem=K` -> `booking_cancel` |
| GET | `/booking/:id/status` | Escaped derived booking status (404 unknown) |
| POST | `/restaurant/table/open` | body `session=S&venue=V&table=T&party=N&idem=K` -> `table_open_session` |
| POST | `/restaurant/order/line` | body `session=S&line=L&sku=P&qty=N&mods=M&idem=K` -> `order_add_line` |
| POST | `/restaurant/kitchen/ready` | body `session=S&line=L&idem=K` -> `kitchen_mark_ready` |
| POST | `/restaurant/line/served` | body `session=S&line=L&idem=K` -> `line_mark_served` |
| POST | `/restaurant/bill/close` | body `session=S&idem=K` -> `bill_close_session` |
| GET | `/restaurant/session/:table/view` | Escaped lines + served total of the table's ACTIVE session (404 `no-session` when free) |
| GET | `/admin/dashboard` | Read-only escaped per-tenant summary (admin role via frozen `role_allows`): products, orders, bookings, open table sessions, outbox pending (`outbox_worker_pending` — run `outbox_worker_setup` once on the store), audit chain OK (`audit_verify_chain`) |

Dispatch order for every request: limits -> path safety -> authenticated
session (`session_valid`, the only auth scheme) -> route. Denial mapping
(frozen in `web_common.deny`): invalid-session 401, forbidden 403,
not-found / no-session / line-not-found 404, conflict / table-occupied /
session-closed / invalid-transition / unserved-lines / stock/record
conflicts 409; idempotent replay returns 200 with the recorded
`duplicate-key` result.

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
- `test/03_system/app/enterprise/enterprise_web_app_spec.spl` — W3-B:
  booking flow incl. conflict 409, restaurant flow incl. invalid-transition /
  table-occupied / session-closed 409, admin dashboard counts + hostile-name
  escaping + 403 for non-admin, 401 on every new route family, idempotent
  hold replay = one effect.

Run one at a time: `bin/simple test <spec>` (interpreter-mode evidence;
per-scenario db paths because the interpreter caches sqlite per path).

## Docgen note

`bin/simple spipe-docgen <spec> --output doc/06_spec --no-index` works on
Linux via an in-app `/proc/self/cmdline` argv-recovery fallback — the Rust
seed's subcommand delegation drops argv (open bug:
`doc/08_tracking/bug/spipe_docgen_subcommand_argv_drop_2026-08-16.md`). On
non-procfs platforms use the direct form:
`bin/simple run src/app/spipe_docgen/spipe_docgen/main.spl <spec> --output doc/06_spec --no-index`.

## Authentication and throttling (W5-A)

Production entry: `store_app_handle_bearer(store, tenant, method, path,
headers, body, now_epoch, entropy)` in
`src/app/enterprise_store_app/auth_routes.spl`. The explicit-session
`store_app_handle` stays for tests; the bearer variant resolves the
`SessionContext` from `Authorization: Bearer <token>` via the durable
session store `std.enterprise_session`
(`src/lib/nogc_sync_mut/enterprise_session/`), then delegates to the same
hardened route path. Determinism: the caller supplies `now_epoch` and login
`entropy` — the library never reads a wall clock or randomness.

- **Credentials** — insert-only `credentials` rows: tenant, actor, role,
  salt, sha256 salted-hash secret (never plaintext). Seeded via the
  admin-guarded `credential_seed` (session_valid + role_allows rung order).
- **`POST /auth/login`** — form `user`/`secret` (+ optional `ttl`); success
  returns `token=<sha256>` in the body (no cookies); failure is a generic
  401 `invalid-credentials` for both unknown user and wrong secret (no
  user enumeration).
- **`POST /auth/logout`** — writes an insert-only revocation row.
- **Resolution** — missing / revoked / expired
  (`now_epoch >= issued_at + ttl`) all collapse to 401.
- **Throttling** — `std.enterprise_session.throttle`: deterministic
  fixed-window counter over insert-only `throttle_hits` rows,
  window = `now_epoch / window_secs`. General key `tenant|token-or-anon`,
  30/60s; login key `tenant|login:user`, 5/60s (anti-brute-force). Over
  limit -> 429 with the shared security headers; rejections record nothing,
  so a denied burst cannot extend its own lockout.

Spec: `test/03_system/app/enterprise/enterprise_auth_throttle_spec.spl` —
login + bearer authorization, generic 401, revocation, expiry (red-first),
replayed-login token idempotency, tenant isolation, 429-then-window-advance,
login brute-force window.
