# Feature: simple_enterprise_suite

## Raw Request
Goal set: with spipe skill impl simple enterprise suite, with simple web/db server harden.
Full research/design/plan: doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md
(assessment verdict: ~8–12% of the requested enterprise product exists today; the
existing `examples/12_business/simple_erp` + `ormastes/simple-erp` prototype is an
in-memory proof of architecture, blocked on durable storage, live identity, and
server hardening).

## Task Type
feature

## Refined Goal
Deliver the Simple Enterprise Suite production foundation per the 2026-08-14
assessment: a shared hardened HTTP core used by both sync and async servers, a
durable database layer (SQLite-backed repository/unit-of-work/migrations/outbox
now; PostgreSQL adapter interface frozen), live tenant/identity/RBAC/audit
foundation, and the first goods-sale proving vertical (catalog → order → stock →
payment state → journal), replacing the in-memory ERP prototype's storage and
route simulation.

## Acceptance Criteria
Wave A — web-server harden (shared HTTP core):
- AC-1: Sync and async HTTP servers consume ONE shared protocol core
  (parser, request limits, header validation, path normalization/safety,
  routing, security policy) — no duplicated parser/router logic; specs for the
  limit/path/smuggling corpus pass against BOTH transports in interpreter mode.
- AC-2: Async parser enforces request-line/header-count/header-line/body/chunk
  limits DURING parsing (before buffer growth), matching the sync limits landed
  in the `webserver_harden` lane; boundary and boundary+1 specs per limit.
- AC-3: Async static-file path is confined: shared `path_is_safe`-equivalent
  guard (decode-once, reject NUL/backslash/encoded separators/double
  encoding/traversal, canonicalize, verify under root); spec proves rejection
  on the async route.
- AC-4: A live system spec proves dynamic route dispatch: a registered handler
  (not the inline static handler) is invoked under a server-established
  security context; duplicate/conflicting Content-Length + Transfer-Encoding
  ambiguity rejected on both transports.

Wave B — db-server harden (durable persistence):
- AC-5: A repository/unit-of-work/transaction/migration interface exists in
  pure Simple with a SQLite adapter (existing sqlite_sffi) providing: migration
  version table, WAL + busy-timeout, enforced foreign keys, prepared-statement
  repositories, typed row mapping; specs prove commit/rollback, idempotency-key
  unique-constraint rejection, and migration up/re-run no-op.
- AC-6: Transactional outbox + append-only audit record land in the same
  transaction as a domain mutation; spec proves a command's domain write and
  outbox row are atomic (both present after commit, both absent after
  rollback), and the audit record uses a real cryptographic digest (std crypto
  sha256), replacing the durable_log toy checksum.
- AC-7: Simple DB (SDN/embedded) is NOT wired as the enterprise store; the
  PostgreSQL adapter is represented only as a frozen interface + explicit
  `blocked/unavailable` row in evidence (no fake driver), per assessment §4.

Wave C — foundation + goods-sale vertical:
- AC-8: Foundation contracts frozen and implemented in the ERP module set:
  TenantContext/ActorContext, Money/Quantity/typed IDs, CommandEnvelope/
  CommandResult/ErrorCode, DomainEvent/OutboxRecord/AuditRecord; the existing
  guarded-write gate (session → RBAC → validation → idempotency) is rewired to
  run over the durable repository layer instead of in-memory arrays; existing
  ERP kernel/lane specs still pass.
- AC-9: Goods-sale vertical passes end-to-end as a system spec: product/SKU +
  price snapshot → order with idempotency key → stock reservation (no negative
  available stock) → payment state transition → balanced journal posting →
  refund/return reverses correctly; retried command with same idempotency key
  produces exactly one effect; state survives process restart (reopen DB,
  re-verify).
- AC-10: Tenant isolation negative test: a command carrying tenant A's session
  cannot read or mutate tenant B's rows through any repository in the vertical.

Cross-cutting:
- AC-11: All new specs are modern SSpec scenario manuals (step("..."),
  outcome-named its, captures where user-facing); `bin/simple spipe-docgen`
  mirrors to doc/06_spec with 0 stubs; no source-text/grep assertions as
  evidence; equality checks paired with absolute oracles.
- AC-12: Docs freshness gate: doc/07_guide pages for http_server, database, and
  the ERP example are updated to describe the shared HTTP core, durable layer,
  and vertical; the research doc cross-link in
  doc/01_research/local/simple_erp.md stays current.

## Scope Exclusions
- No public direct TLS/HTTP2 exposure work (edge-proxy deployment assumed, per
  assessment §3.2 P0-F). TLS/H2 hardening is a separate future lane.
- No real PostgreSQL driver implementation (interface freeze only).
- No payment-provider, Amazon/channel-hub, HCM/payroll, booking/rental,
  restaurant/device, or UI/POS work in this lane — later waves per assessment
  §10.3 (Waves 3–5).
- No Simple DB (MVCC/WAL server) work.
- No microservice decomposition; modular monolith only.
- Native `Dict.get()` corruption / exit-139 toolchain defects are tracked
  compiler bugs, not fixed here; specs run interpreter-mode with native rows
  recorded blocked where affected.

## Cooperative Review
- Sidecars: Claude Sonnet for Wave A transport-parity specs and Wave B SQLite
  adapter specs; Claude Haiku for boundary/boundary+1 limit spec fan-out.
- Merge owner: orchestrating session (this lane).
- Final reviewer: Opus/highest-capability review before implement-done; auth,
  transaction-atomicity, and idempotency code requires high-model review per
  assessment §12.4.
- Shared interface names (freeze in architecture phase): `HttpCore` modules
  (`request_parser`, `request_limits`, `path_normalization`, `routing`,
  `security_policy`); persistence `Repository`, `UnitOfWork`, `Migration`,
  `OutboxRecord`, `AuditRecord`; foundation `TenantContext`, `ActorContext`,
  `CommandEnvelope`, `CommandResult`.
- Manual step helpers: `step("Open a tenant session")`, `step("Submit the
  guarded command")`, `step("Reopen the database and verify state")`,
  `step("Replay the command with the same idempotency key")`.
- Setup/checker helpers: `setup_enterprise_db(path)`, `checker_journal_balanced`,
  `checker_stock_nonnegative`, `checker_outbox_atomic` — placeholders must
  `fail(...)` explicitly.
- Generated-manual review owner: final reviewer (same as above).

## Phase
implement (Wave A in progress)

## Log
- dev (2026-08-14): Lane created from the enterprise-suite assessment
  (doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md).
  Goal scoped to assessment Waves 0–2 equivalents: shared hardened HTTP core
  (extends the completed `webserver_harden` sync-only lane to async parity),
  durable SQLite-backed repository/outbox/audit layer, frozen foundation
  contracts, and the goods-sale proving vertical. Booking/restaurant/channels/
  HCM and PostgreSQL driver explicitly deferred to follow-up lanes. Next phase:
  research → arch (contract freeze) → spec → implement → verify.
- implement Wave A slice 1 (2026-08-14): Shared protocol core landed at
  src/lib/common/net/http_core.spl (limits, content_length_from_text,
  body_decision(allow_chunked) incl. CL+TE-chunked 400 smuggling-ambiguity
  rejection, path_is_safe, NEW bounded decode_chunked_bounded/hex_chunk_size).
  Sync parser/router now delegate via `export use` (66/66 sync spec cases
  green: chunked 13, parser_limits 23, path_safety 30). Async parser enforces
  limits DURING parse (request-line/header-line/header-count growth bounds,
  body 413 pre-buffer, chunked raw-accumulation + decoded-size bounds) via
  HttpRequestParser.with_limits; dropped dependency on std.http.headers
  decode_chunked (its `index_of as common_index_of` alias is unresolvable on
  the deployed interpreter — pre-existing defect, routed around via core
  decoder). Async router rejects unsafe paths pre-matching (ParseError 400);
  worker maps that to send_error 400 and inline_static_handler has a
  defence-in-depth path_is_safe guard before root+path concatenation.
  New specs green: http_core_spec 23/23, async_parser_limits_spec 18/18,
  async_path_safety_spec 8/8. Regression: worker_static_file 4/4,
  phase_result_headers 16/16; protocol_handler_spec 7/8 — the 1 failure is a
  PRE-EXISTING string-vs-integer semantic mismatch in that spec's own case
  (file untouched by this lane). Runner: bin/release/aarch64-apple-darwin/simple
  (Jul-25 stage4 full CLI; the macho-dir binary is currently a bootstrap-only
  build without `test`). Follow-ups: (a) async router still duplicates
  match_route_pattern/extract_route_params from sync — fold into core with
  parity specs; (b) std.http.{limits,path_security} tier-copied modules overlap
  this policy and appear unwired into the async request path — unify onto
  http_core; (c) AC-4 dynamic dispatch wiring in worker.process_request still
  calls inline_static_handler unconditionally (assessment P0-D) — next slice.
- implement Wave A slice 2 (2026-08-14): AC-4 dispatch wired — worker
  process_request now routes non-static handler_type through
  execute_handler_with_remote_security_context (registry + task security
  context); pure is_dynamic_handler decision fn added. AC-1 routing dedup —
  match_route_pattern/extract_route_params moved into http_core; sync router
  re-exports, async router imports (its former local copies deleted). New
  spec async_dynamic_dispatch_spec 6/6 (registered handler runs, observes
  transport identity, context cleared after dispatch, empty registry → 501).
  Re-runs green: async_path_safety 8/8, sync path_safety 30/30,
  parser_limits 23/23, http_core 23/23, async_parser_limits 18/18.
  Docgen: manuals generated for all 4 new specs (http_core manual OK at 104
  doc lines; async three WARN <100 lines; the only "stub" counted is the
  docgen tool's own AUTO `main` doc — pre-existing quirk, not lane specs).
  New guide doc/07_guide/lib/networking/http_server_hardening.md (+_tldr).
  EVIDENCE CAVEAT: runner bin/release/aarch64-apple-darwin/simple prints the
  Rust-seed banner on some commands — spec evidence is interpreter-mode
  diagnostic; re-verify on a fresh stage4 self-hosted deploy (the current
  macho-dir deploy is bootstrap-only, no `test`) before release claims.
  Remaining for Wave A verify: live-socket system spec for dynamic dispatch;
  unify std.http.{limits,path_security} tier copies onto http_core.
