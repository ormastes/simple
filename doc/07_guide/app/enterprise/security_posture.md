# Enterprise Suite — Security Posture (W9-D adversarial audit)

Lane `.spipe/simple_enterprise_suite`, lane W9-D. This is the audit record for
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

Four attacks succeeded. All four are fixed and fenced by the spec.

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

## Residual risks (honest)

1. **Entropy quality is still the caller's responsibility.** The derivation is
   now collision-free and not cross-derivable, but a deployment that supplies a
   guessable constant still weakens brute-force resistance for its *own*
   actor's token if the attacker also learns that actor's `secret_hash`. The
   library performs no randomness reads by design; the deployment must feed a
   real CSPRNG.
2. **The provider seam is still a stand-in, not PCI evidence.** The signature
   is `sha256(shared_secret | material)`, not a real provider HMAC scheme with
   timestamp tolerance. It is not constant-time compared. Replacing the seam
   with a provider SDK is a one-struct change.
3. **Throttle counting is a full table scan.** `throttle_count` scans all
   `throttle_hits` rows for every admitted request, and rows are insert-only
   with no pruning. A sustained flood therefore makes each *subsequent* request
   more expensive — an amplification surface the fixed window bounds only per
   window, not over time. A pruning sweep or an indexed count is the follow-up.
4. **`role_allows` is a hardcoded role table, not a registry.** Back-office
   reads reuse an existing write action (`hcm.leave.decide`,
   `proc.requisition.approve`, `finance.period.close`) as their read grant, so
   read and write authority are not separable per role today.
5. **`form_value` cannot express values containing `&` or `=`,** and does no
   percent-decoding. Business identifiers carrying those characters silently
   parse as empty rather than being rejected.
6. **No CSRF token and no cookie flow.** The app is bearer-token only, which
   sidesteps CSRF; introducing cookies would require this to be revisited.
7. **`/booking/*` and `/restaurant/*` reads are authenticated but not
   role-gated** — any active session in the tenant may read them. That is the
   deliberate customer-facing posture, not an oversight, but it is stated here
   so a future privacy-sensitive field on those pages gets a second look.

## Related

- `doc/07_guide/app/enterprise/guarded_command_contract.md` — the rung order
  every guarded command follows.
- `doc/06_spec/.../enterprise_security_audit_spec.md` — generated spec doc.
