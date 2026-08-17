# Enterprise Suite — Security Posture (W9-D audit, W12-B residual-risk closure)

Lane `.spipe/simple_enterprise_suite`, lanes W9-D and W12-B. This is the audit record for
the suite's trust boundaries: what was attacked, what the attack actually did,
and what changed. The authoritative, executable form of everything here is
`test/03_system/app/enterprise/enterprise_security_audit_spec.spl` — this page
summarises it; the spec is what bites.

Evidence: interpreter mode, Rust seed
`bin/release/x86_64-unknown-linux-gnu/simple` (59537008 bytes, 2026-08-16),
`SIMPLE_TIMEOUT_SECONDS=900`, one spec per run, one db path per scenario.

## Attack matrix

| # | Attack | Probed through | Result BEFORE | Fix | Now |
|---|--------|----------------|---------------|-----|-----|
| 1 | Tenant isolation — tenant-B session reads tenant-A catalog / roster / POs / resources / dashboard roll-up | `store_app_handle` on 5 routes | **safe** — every read filters on `tenant.tenant_id`, the session tenant, never a payload tenant | none needed | regression test |
| 1b | Tenant isolation — tenant-B mutates tenant-A order / PO receipt / employee clock-in | `/store/order`, `/proc/receive`, `/hcm/clock/in` | **safe** — 404/409, nothing written into tenant-A's streams | none needed | regression test |
| 2 | Authorization — `sales` role reaches a back-office action via a different route sharing the command | 11 routes (`/admin/dashboard`, `/hcm/*`, `/proc/*`, `/fin/*`) | **safe** — every back-office read re-checks `role_allows` at the route, and every write re-checks inside the guarded command | none needed | regression test |
| 3a | Session — revoked / expired / cross-tenant bearer token | `store_app_handle_bearer` | **safe** — 401 on read, write, and logout | none needed | regression test |
| 3b | Session — token guessable when the caller supplies CONSTANT entropy | `session_issue` | **ATTACK SUCCEEDED.** Token was `sha256(entropy \| tenant \| actor \| now)`. Two logins for one actor in the same second produced the *same* token, and any party knowing the constant entropy could derive **any** actor's token from public inputs | `session_token_derive` now also binds the actor's server-side `secret_hash` and a per-store issuance sequence (`session_issued_count`) | fails closed |
| 4a | Injection — SQL payload through a form value | `POST /store/order` with `'; DROP TABLE products;--` | **safe** — all writes go through prepared binds; the payload lands as data, catalog reads still work | none needed | regression test |
| 4b | XSS — supplier name, employee name, booking resource id, seat-map version, restaurant table id (reflected via `deny()` detail), receipt id | 6 rendered surfaces | **safe** — every surface renders through `esc()`, no raw `<script>` anywhere | none needed | regression test |
| 4c | Path traversal via route parameter, raw / percent-encoded / NUL | 3 shapes | **safe** — `path_is_safe` rejects all three with 400 before any route logic | none needed | regression test |
| 5a | Payment — webhook signature lifted from one event onto another | `payment_webhook_receive` | **ATTACK SUCCEEDED.** The signature covered only `envelope.payload`. A valid capture signature for intent 1 was replayed with intent 2's `provider_ref` and a fresh `provider_event_id`, and **captured the second order and marked it paid** | signature now covers `webhook_signing_material` = `pwh/v2 \| tenant \| provider_ref \| event_kind \| provider_event_id \| payload`; `provider_sign_webhook` / `provider_verify_webhook` added | fails closed for ref-swap, kind-swap, event-id-swap, and legacy payload-only signatures |
| 5b | Payment — replay a tenant-A webhook against tenant-B | `payment_webhook_receive` | **safe** — `payment_intent_by_ref` is tenant-scoped (`not-found`); now also signature-bound to the tenant | strengthened | regression test |
| 6a | DoS — 20 MB unauthenticated login body | `POST /auth/login` | **ATTACK SUCCEEDED.** `body_decision` ran only inside `store_app_handle`, so the auth routes — the only unauthenticated surface — never applied it. 200 | `body_decision` moved to rung 0 of `store_app_handle_bearer` | 413 (and 400/501 for smuggling shapes) |
| 6b | DoS — credential stuffing by rotating the `user` form field | `POST /auth/login` x40 | **ATTACK SUCCEEDED.** The only login throttle was keyed `tenant\|login:<user>`, a caller-controlled field; rotating it made the lockout unreachable and left the login path with no limit at all | a login is now charged to the tenant-wide `tenant\|anon` window *first*, then the per-user window | 429 |
| 6c | DoS — slow-burn amplification through the throttle's OWN counter table (W12-B; was residual risk 3) | `throttle_admit` x900 across 300 windows | **DEFECT CONFIRMED.** `throttle_hits` was insert-only with no pruning and `throttle_count` scanned all of it, so every admitted request made the *next* one more expensive — the defence was the bottleneck. With the sweep removed the spec does not fail, it **never finishes**: killed at `SIMPLE_TIMEOUT_SECONDS=900` | `throttle_prune` drops the counter table once every retained row belongs to an elapsed window; the predicate is evaluated in pure Simple, the delete is `store_truncate` | rows retained bounded by the LIVE window (measured <= 6 after 900 admits), counts still exact across the boundary |
| 8 | Filter bypass — an encoded separator in a form value (W12-B; was residual risk 5) | `form_value` + every route that reads a body | **DEFECT CONFIRMED.** `form_value` split on `&` and `=` and did no percent-decoding, so `a=x%26y` yielded the raw `x%26y`, `a=x=y` yielded nothing at all, and anything downstream that inspected the value (escaping, digit checks, id lookups) saw text that was not what the client sent | `percent_decode` — one pass, `+` -> space, `%XX` -> byte, and FAIL CLOSED on truncated / non-hex / `%00`; `form_value` splits on the first `=` only | full parsing table specced; the escaping specs are unchanged and still green (a decoded `<script>` still renders `&lt;script&gt;`) |
| 9 | Authorization — `/booking/*` and `/restaurant/*` reads reachable by any authenticated role (W12-B; was residual risk 7) | `store_app_handle` on 3 reads with a `sales` session | **DEFECT CONFIRMED (reclassified).** W9-D recorded this as "the deliberate customer-facing posture". It is not: there is no customer role and no per-customer scoping in this app, so "customer-facing" meant every role in the tenant — a `sales` session could enumerate the resource inventory, probe any booking id, and walk table ids to read every open bill (lines, quantities, modifiers, totals) with no ownership proof | both families' reads now re-check the FROZEN `role_allows` with the family's own action (`booking.hold`, `restaurant.table.open`), exactly as the back-office families do | 403 for `sales`; `booking` role reads its own family and is 403 on the restaurant bill view; `admin` unchanged |

Four attacks succeeded in the W9-D pass; W12-B confirmed and closed three more
defects that W9-D had deferred as residual. All seven are fixed and fenced by
the spec.

## The fixes

- `src/lib/nogc_sync_mut/enterprise_session/session.spl` —
  `session_token_derive(entropy, tenant, actor, now, binding, seq)`; `binding`
  is the credential's stored `secret_hash`, `seq` is `session_issued_count`.
  Both are server-side and unobservable to a requester.
- `src/lib/nogc_sync_mut/enterprise_payment/payment.spl` —
  `webhook_signing_material` / `provider_sign_webhook` /
  `provider_verify_webhook`; `payment_webhook_receive` verifies the bound
  material instead of the bare payload.
- `src/app/enterprise_store_app/auth_routes.spl` — `body_decision` as rung 0
  for every request; tenant-wide anonymous throttle applied to logins.

### W12-B (2026-08-17)

- `src/lib/nogc_sync_mut/enterprise_session/throttle.spl` — `throttle_prune`
  + `throttle_rows_retained`; `throttle_admit` sweeps before it decides, on
  the reject path too.
- `src/lib/nogc_sync_mut/enterprise_store/store.spl` — `store_truncate`, the
  only delete in the suite. **Deliberately unconditional:** the Rust seed's
  interpreter SQLite emulation parses `DELETE FROM <t>` and then clears the
  whole table, silently ignoring any WHERE clause, so a conditional delete
  means two different programs in interpreter vs native mode. Filed as
  `doc/08_tracking/bug/seed_sqlite_emulation_ignores_delete_where_2026-08-17.md`.
  The throttle establishes the predicate itself before calling.
- `src/app/enterprise_store_app/web_common.spl` — `percent_decode` and the
  rewritten `form_value` (parsing table in the source docstring).
- `src/app/enterprise_store_app/booking_routes.spl`,
  `restaurant_routes.spl` — `role_allows` re-checked on the reads.

Red-first evidence (interpreter mode, Rust seed 59536728 bytes 2026-08-16,
`SIMPLE_TIMEOUT_SECONDS=900`, one spec per run), all against
`enterprise_security_audit_spec.spl` at `declared>=12 executed=12`:

| sabotage | verdict |
|---|---|
| `throttle_prune` call removed | **never finishes** — killed at 900s (the amplification itself) |
| prune made unconditional (staleness predicate bypassed) | passed=10 failed=2 (count correctness AND the 6b login-throttle scenario) |
| `form_value` reverted to the pre-W12-B naive parser | passed=10 failed=2 |
| both role gates forced open | passed=11 failed=1 |
| none (restored) | **passed=12 failed=0** |

### W13-C (2026-08-17)

Evidence: interpreter mode, Rust seed
`bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes, 2026-08-16),
`SIMPLE_TIMEOUT_SECONDS=900`, one spec per run.

- **Residual 1 (entropy quality) — audited, no production weak-entropy path
  exists.** Every issuer of a session token goes through `session_issue`;
  its only non-spec caller is `store_app_handle_bearer`
  (`auth_routes.spl:101`), which takes `entropy` as a parameter — there is
  no daemon in the repo that wires a constant. All weak/short entropy values
  found were SPEC literals. Per the audit contract, a defensive boundary
  check was added instead of trusting the caller:
  `session_issue` now denies (generic `invalid-credentials`, no oracle) any
  entropy under `session_entropy_min_len()` = 8 bytes
  (`enterprise_session/session.spl`). Distinct-token-under-identical-inputs
  was already fenced (the CONSTANT-entropy scenario); the new boundary
  scenario is `enterprise_security_audit_spec` "rejects entropy too short to
  have come from a CSPRNG". Sabotage (check reverted to `entropy == ""`):
  passed=12 failed=1; restored: passed=13 failed=0. Spec-only short
  entropies (`"e-lock"` etc. in `enterprise_auth_throttle_spec`) were
  lengthened.
- **Residual 7 (byte-wise percent-decode) — verified SAFE for multi-byte
  UTF-8, fenced.** Probe + spec confirm `%C3%A9` (2-byte) and `%E2%82%AC`
  (3-byte) decode byte-wise (mojibake, as documented) but every decoded byte
  of a multi-byte sequence is >= 0x80, so no `<`, `>` or quote can be
  manufactured from inside a sequence; a real `%3C` after a multi-byte value
  still renders through `esc()` as `&lt;`. No XSS. Regression fences assert
  presence AND exact byte-length of the decoded sequences (a first, weaker
  fence that only checked absence-of-`<` survived a byte-dropping sabotage
  and was strengthened). Sabotage (decoder drops bytes >= 0x80): passed=12
  failed=1; restored: passed=13 failed=0. The charset-recombination gap
  itself remains residual (renumbered 6 below).
- **Gap check — two guarded commands never adversarially exercised for
  cross-tenant mutation:** `sale_refund_order` (against a seeded PAID
  tenant-A order) and `proc_receive` (against a seeded open tenant-A PO)
  added to the conformance tenancy scenario (now 17 denials, all
  `invalid-session`, state fingerprint byte-identical). **No cross-tenant
  mutation succeeded.** Sabotage (tenant rung of `session_valid` forced
  open): passed=7 failed=1; restored: passed=8 failed=0.

Regression (one spec at a time): `enterprise_security_audit_spec` 13/13,
`enterprise_auth_throttle_spec` 6/6, `enterprise_conformance_spec` 8/8,
`back_office_web_spec` 7/7, `store_app_spec` 3/3.

## Residual risks (honest)

Risk 1 of the W9-D list is CLOSED by W13-C (boundary check above); risk 7's
XSS question is answered safe and fenced, with only the
charset-recombination remainder kept (item 6).

1. **The provider seam is still a stand-in, not PCI evidence.** The signature
   is `sha256(shared_secret | material)`, not a real provider HMAC scheme with
   timestamp tolerance. It is not constant-time compared. Replacing the seam
   with a provider SDK is a one-struct change.
Risks 3, 5 and 7 of the W9-D list are CLOSED by W12-B — they are rows 6c, 8
and 9 of the matrix above. What remains:

2. **`role_allows` is a hardcoded role table, not a registry.** Every
   role-gated read reuses an existing write action as its read grant
   (`hcm.leave.decide`, `proc.requisition.approve`, `finance.period.close`,
   and now `booking.hold`, `restaurant.table.open`), so read and write
   authority are not separable per role. W12-B widened the surface this
   applies to rather than fixing it: gating the booking and restaurant reads
   made the app CONSISTENT, not finer-grained. Concretely, no role can be
   granted "read the open bill" without also being granted "open a table".
3. **No CSRF token and no cookie flow.** The app is bearer-token only, which
   sidesteps CSRF; introducing cookies would require this to be revisited.
4. **The throttle is bounded but still a linear scan of the live window.**
   `throttle_count` walks the whole retained set rather than an index. The
   set is now bounded by the live window instead of by all traffic ever, so
   the amplification is gone, but the per-request cost is still O(live window
   traffic), not O(1). An index on `(key, window)` is the follow-up.
5. **The throttle sweep is all-or-nothing.** `throttle_prune` fires only when
   EVERY retained row is stale. A key that is exercised without pause across
   a boundary keeps its window's rows alive and blocks the sweep for all
   other keys in that instant; the next boundary with a genuine gap clears
   them. This is a consequence of the seed's DELETE defect above (no
   per-row delete is available), and it can only cost boundedness — it can
   never let a request past a limit.
6. **`percent_decode` decodes bytes, not characters.** `%C3%A9` yields two
   separate bytes appended as text rather than one `é`. W13-C verified this
   cannot smuggle markup (all bytes of a multi-byte sequence are >= 0x80)
   and fenced it, so the remainder is purely the mojibake/normalisation gap:
   no route compares business identifiers after Unicode normalisation today,
   but a future field that does would need recombination added deliberately.
7. **Nothing role-gates a WRITE at the route.** Writes are gated inside the
   guarded commands (rung order in `guarded_command_contract.md`), which is
   where the authority actually lives; the route-level checks added by W12-B
   cover reads only. This is by design — two gates for one decision is how
   they drift — but it means a route added without a guarded command behind
   it inherits no authorization at all.

## W14-A — output-escaping + security-header completeness audit (2026-08-17)

A reproduce-first sweep of EVERY interpolation of a request- or store-derived
value into HTML across `booking_routes`, `restaurant_routes`, `dashboard`,
`auth_routes`, `hcm_routes`, `procurement_routes`, `finance_routes`, and
`web_common`. Conclusion: **already hardened — no unescaped attacker-influenceable
interpolation, and no response path omits the security headers.** Full
path:function -> escaped? audit list:
`doc/01_research/app/enterprise/w14a_output_escaping_audit_2026-08-17.md`.

Findings, all confirming safety (like W13-C):

- **Every dynamic value passes through `esc()`.** All page renders interpolate
  only store-/library-derived values (`sqlite_row_get`, `booking_status`, ledger
  lines, employee/PO fields) or URL params, each wrapped in `esc()`. The
  literal `esc("{wage}")`-style tokens are static placeholder strings, not data.
- **`esc()` is attribute-context safe, not merely element-safe.** It escapes
  `"`->`&quot;` and `'`->`&#39;` in addition to `&`/`<`/`>`. Every attribute in
  the app is double-quoted (`data-resource`, `data-line`, `data-po`,
  `data-account`, `data-employee`, `data-ref`), so a `">`-prefixed breakout
  cannot escape the attribute. This was untested before W14-A (the prior fence
  only exercised element context on `/store/catalog`) and is now fenced.
- **Every response path is wrapped by `secured()`/`with_default_security_headers`
  — including denials.** `deny()`, `command_page`, the trailing `404`, and the
  auth `too_many()`/`unauthorized()`/`413`/`501`/`400` returns all wrap; a grep
  for any unwrapped `HttpResponse.{html,error,...}` across the seven route files
  returns nothing.
- **`auth_routes` `"token=" + r.detail` (line 104) is NOT escaped but is safe by
  source:** `r.detail` is the freshly issued session token derived from the
  server-supplied `entropy` (see attack #3b), never an attacker-influenceable
  field.

Fence: `test/03_system/app/enterprise/enterprise_output_escaping_audit_spec.spl`
(declared>=5 executed=5 passed=5). Red-first proof: temporarily disabling the
`"`->`&quot;` replacement in `esc()` flips 3 of the 5 to red (the attribute-
context assertions + the booking-resource breakout), restored to green — so the
fence bites the exact attribute-context gap it claims to cover. Evidence:
interpreter mode, Rust seed `bin/release/x86_64-unknown-linux-gnu/simple`
(59536728 bytes, 2026-08-16), `SIMPLE_TIMEOUT_SECONDS=900`, one spec per run.

## Related

- `doc/07_guide/app/enterprise/guarded_command_contract.md` — the rung order
  every guarded command follows.
- `doc/06_spec/.../enterprise_security_audit_spec.md` — generated spec doc.
