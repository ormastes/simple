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
- AC-8a: Foundation contracts frozen and implemented over the durable layer:
  TenantContext/ActorContext/SessionContext, Money, CommandEnvelope/
  CommandResult with a closed reason set; the guarded-write sequence
  (session → RBAC → validation → idempotency → effects-in-one-UoW) is
  implemented over the durable repository layer (std.enterprise_sale).
- AC-8b (amended 2026-08-14, split from AC-8): the existing
  examples/12_business/simple_erp lanes are rewired onto
  std.enterprise_{store,sale} (replacing in-memory arrays/used_keys) and the
  example's ubs_test suite still passes. Reason for split: the example is a
  self-contained project with local imports and its own test harness; wiring
  it is an independent, testable increment that must not gate the stdlib
  vertical evidence.
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
- implement Wave B (2026-08-14): std.enterprise_store landed
  (src/lib/nogc_sync_mut/enterprise_store/{store,records}.spl + async-tier
  wrapper): store_open with WAL/busy-timeout/FK pragmas + system tables,
  HONEST backend ACID probe (insert→rollback→count), uow_begin/commit/
  rollback, named migrations (re-run no-op), idempotency keys, transactional
  outbox, sha256-chained audit log (replaces toy checksum; AC-6). Spec
  enterprise_store_spec 10/10 incl. tamper detection, tenant scoping,
  restart survival. CRITICAL FINDING filed: interpreter rt_sqlite externs are
  a NON-ACID emulation (begin/commit/rollback return 1 ignoring args;
  constraints unenforced; WHERE-equality ignored; UPDATE unsupported; per-path
  in-process db cache) —
  doc/08_tracking/bug/interpreter_sqlite_externs_nonacid_emulation_2026-08-14.md.
  Store design routes around it (insert-only tables, pure-Simple filtering,
  prepared binds); ACID atomicity evidence (AC-5/AC-6 atomic commit half)
  is environment-blocked on the interpreter — resume: run the same specs
  --mode=native with real SQLite once the native lane is unblocked. AC-7
  honored: PostgreSQL = frozen interface documented in store.spl docstring +
  guide; no fake driver.
- implement Wave C slice 1 (2026-08-14): std.enterprise_sale landed
  (foundation.spl frozen contracts: TenantContext/ActorContext/SessionContext/
  Money/CommandEnvelope/CommandResult + closed reason set; goods_sale.spl:
  catalog, insert-only stock ledger, order event stream, double-entry journal,
  guarded sale_place_order/sale_pay_order/sale_refund_order with the frozen
  sequence session→rbac→validation→idempotency→effects-in-one-UoW).
  System spec goods_sale_vertical_spec 7/7: full sell→pay→refund with
  balanced journal + audit chain; all four guard rungs denied with exact
  reasons; idempotent replay = exactly one effect (stock+outbox unchanged);
  tenant isolation (AC-10) incl. cross-tenant session rejection; restart
  survival with post-restart replay guard. Spec landmine learned: interpreter
  sqlite caches per path in-process → one db path per scenario.
  AC-8a done (contracts + guarded gate over durable repos in stdlib);
  AC-8b (example-lane rewiring + ubs_test) split out and open — see amended
  Acceptance Criteria. Guides: doc/07_guide/lib/database/enterprise_store.md
  (+_tldr).
- review fixes (2026-08-14, advisor pass): Money threaded through
  sale_add_product (was exported-unused); journal-balance docstring aligned
  with implementation (per-tenant check; per-order balance by construction
  via post_journal pairs); protocol_handler_spec 7/8 attribution CONFIRMED
  pre-existing (its imports are tls_handshake/tls_common/protocol_handler
  only — none touched by this lane). Vertical spec re-run 7/7 after Money
  change. LLM wiki entry created:
  doc/00_llm_process/feature_expert/enterprise_suite/skill.md.
- rebase merge (2026-08-14 late): origin main was force-rewritten by parallel
  sessions; chain rebased with a two-sided hand-merge at the root per vcs.md
  (diff both directions). Kept from origin's parallel `wip(servers)` work:
  RUNTIME_READ_LINE_CAP truncation detection, parse_request_with_policy_limits
  (read-iteration cap), strict request-line grammar, _method_supported 501,
  singleton-security-header dedup (MOVED into http_core body_decision so async
  gets it too), and the boundary-aware chunked terminator ALGORITHM (ported
  into http_core as chunked_body_end_scan — origin's chunked_body_end/
  decode_chunked in std.http.headers remain unusable on the deployed
  interpreter: `index_of as common_index_of` alias unresolvable; verified by
  fresh probe). Kept from this lane: core delegation, async during-parse
  limits, bounded decode. DELIBERATE DEVIATION from origin: headers_decision
  rejects chunked TE with 501 but accepts non-chunked TE values (origin's
  any-TE-501 contradicts its own still-green chunked_rejection_spec case
  "accepts non-chunked transfer-encoding values"). Async chunked framing now
  fails closed: invalid framing 400 via scan -2 / strict bounded decode.
  Full post-rebase sweep green: http_core 23, sync chunked 13 +
  parser_limits 23 + path_safety 30, async parser 18 + path 8 + dispatch 6,
  enterprise_store 10, goods_sale_vertical 7 (138 cases).
- EVIDENCE STATUS (verify gate, do not close ACs on this alone): all spec
  evidence this session is interpreter-mode on the Jul-25
  bin/release/aarch64-apple-darwin binary (seed-banner caveat). Resume
  condition for verify PASS: fresh stage4 self-hosted deploy, then re-run the
  six verification commands in
  doc/00_llm_process/feature_expert/enterprise_suite/skill.md; ACID rows
  additionally need --mode=native with real SQLite. Owner: next lane session.

## Goal Set v2 (2026-08-16)
Raw request: "with spipe skill, harden simple web and db and web ui. find existing
plan of enterprise app, update it. do not make app on simple os and other os
separately but both runnable. make a complete enterprise app, store app, harden
server and web ui. parallel agents with guide and higher-model review."

Research inputs (saved this session):
- doc/01_research/app/enterprise/simple_enterprise_suite_full_design_2026-08-14.md
- doc/01_research/app/enterprise/simple_enterprise_suite_assessment_and_parallel_plan_2026-08-16.md

New acceptance criteria (extends AC-1..AC-12 above):
- AC-13 (verify gate re-run): re-run the six verification commands from
  doc/00_llm_process/feature_expert/enterprise_suite/skill.md on THIS host's
  runner; record per-spec verdicts; ACID rows stay environment-blocked until a
  native SQLite lane exists (do not fake).
- AC-14 (AC-8b): examples/12_business/simple_erp lanes rewired onto
  std.enterprise_{store,sale}; ubs_test suite green.
- AC-15 (web UI harden): the enterprise dashboard/web UI is served through the
  hardened http_core route path (dynamic dispatch, path safety, limits) with an
  authenticated session; specs prove unauthenticated denial, escaped HTML
  output (no raw interpolation of business data), and security headers.
- AC-16 (store app): a customer-facing store vertical (browse catalog → cart →
  guarded order via sale_place_order → pay → receipt view) built ONLY on
  std.enterprise_{store,sale} + http_core; system spec end-to-end incl.
  idempotent replay and tenant isolation.
- AC-17 (cross-OS runnable, board-runnable rule analog): the enterprise/store
  app is ONE codebase runnable on host OS and SimpleOS — no per-OS forks. Host
  evidence = spec run; SimpleOS evidence = the app's entry compiles for the
  simpleos target or an explicit blocked row naming the missing prerequisite
  (per SimpleOS compiler-in-filesystem contract). QEMU-only or host-only
  silent scoping is a defect.
- AC-18 (db harden continuation): enterprise_store gains corruption-detection
  and disk-full/short-write failure specs at the pure-Simple layer (audit chain
  tamper already covered); document the native-ACID resume condition.

## Parallel lanes (v2)
- L-A verify+AC-8b (agent): AC-13, AC-14.
- L-B store app + web UI (agent): AC-15, AC-16.
- L-C cross-OS + db harden (agent): AC-17, AC-18.
- Review: orchestrating high-model session reviews all lane diffs before
  accepting done marks (assessment §12.4).

## Log (v2)
- dev (2026-08-16): state restored (was deleted by a parallel session's
  cleanup); v2 goal set added; three parallel lanes launched.
- merge + review (2026-08-16, orchestrator high-model): three parallel lane
  worktrees merged. L-A (ent-la 709ea3644cf): AC-13 verify rerun 72/72 across
  the six skill.md specs (interpreter-mode, Rust seed x86_64 — native-ACID rows
  stay environment-blocked); AC-14 done — simple_erp example rewired onto
  std.enterprise_store durable idempotency/audit/outbox, ubs_test 21/21 specs
  163/163 examples. L-B (ent-lb 9b42402f98d): AC-16 store app
  (src/app/enterprise_store_app/main.spl, only enterprise_{store,sale}+
  http_core; escaped HTML; shared security headers) spec 3/3; AC-15 harden
  spec 4/4 (401 unauth, script-name escaping, headers, limits/traversal);
  review fix applied at merge: qty form value digit-checked before int().
  Known tool bug found: seed `spipe-docgen` subcommand drops argv — use
  `bin/simple run src/app/spipe_docgen/spipe_docgen/main.spl <spec> ...`.
  L-C (ent-lc 90e2b6e1b9b): AC-18 corruption detection (store_verify/
  store_open_verified, marker row — interpreter sqlite COUNT is vacuous, noted)
  + injectable write-failure seam (StoreFaults/BufferedUow), harden spec
  deliberate-red 3F then 5/5; regressions 10/10 + 7/7. AC-17: one codebase;
  simpleos cross-compile of store probe → valid SMF; in-guest run blocked on
  missing rt_sqlite_* provider in src/os (resume recorded in guide).
  MERGE HAZARD LOG: a concurrent session staged deletion of the entire
  enterprise stdlib + simple_erp example in the shared WC; restored from HEAD
  per anti-revert protocol and committed blob-first, scoped to this feature's
  paths only.
  (merge note: WC http_server files were a stale pre-hardening snapshot from a parallel session — restored to HEAD per anti-revert protocol; store_app/web_harden/vertical re-verified 3/3, 4/4, 7/7 on the merged tree.)
- merge wave 2 (2026-08-16, orchestrator high-model review): six lanes merged
  onto a24e214200d. W2-A file-backend fallback (store_open composes pure-Simple
  SPLSTORE1 backend when sqlite unavailable; simpleos cross-compile green;
  in-guest run evidence-pending on 4 rt_file_* externs). W2-B http unification
  (3-tier limits/path_security -> thin re-exports of http_core; live-socket
  dynamic dispatch system spec 4/4; REAL DEFECT fixed: sync Router fn-field
  dispatch never worked under interpreter; sync CL+TE ambiguity cases added).
  W2-C spipe-docgen argv-drop root cause + bug doc + /proc/self/cmdline
  fallback; 5 manuals regenerated 0 stubs. W2-D booking vertical
  (std.enterprise_booking, 3 conflict modes, holds/TTL; foundation gains
  closed reason 'conflict' + booking role; 8/8, red-first 5/8). W2-E
  restaurant vertical (std.enterprise_restaurant, 7/7, red-first 4/7; review
  finding: its six new denial reasons were added to the closed set in
  foundation.spl at merge). W2-F outbox worker + reconciliation
  (std.enterprise_outbox, at-least-once + dedup contract, 8/8, red-first 2/8;
  renamed outbox_worker_pending to dodge records.outbox_pending collision).
  Guide enterprise_store.md hand-merged (A/C/F three-way). Research docs
  committed (missed in a24e214). Merge sanity reruns below.
- merge wave 3+4 partial (2026-08-16, orchestrator review): five lanes merged.
  W3-A rt_file_facade guest externs (src/os/userlib/rt_file_facade.spl,
  @export("C") x4; probe cross-compiles w/ all 4 symbols; QEMU rung blocked —
  existing OVMF lanes boot a kernel entry without SMF exec; resume recorded).
  W3-B booking/restaurant/admin-dashboard web routes (web_common/
  booking_routes/restaurant_routes/dashboard siblings behind the same
  hardened prelude; enterprise_web_app_spec 5/5, red-first 4/5).
  W3-C full regression 37/37 (wave-1 six, wave-2 ten, ubs_test 21) + wiki
  refresh (feature_expert/enterprise_suite/skill.md rewritten;
  layer_expert/server_transport_security pointer). W4-B cross-OS gate
  scripts/check/check-enterprise-cross-os.shs (fail-closed + fatal selftest;
  4 probes compile host+simpleos; REAL FIX: sha256_text closure not SMF-safe
  -> audit_hash.spl SMF-safe facade, FIPS digest parity. DEBT: audit_hash is
  a deliberate second sha256 impl; root fix = standalone-SMF codegen support
  for slice/CollectionLiteral, then collapse the facade to a re-export).
  W4-C arch matrix: x86_64/aarch64/riscv64 simpleos SMF PASS unchanged
  codebase; riscv32/i686/armv7 BLOCKED (toolchain, incl. seed --backend llvm
  ignored). W4-A (in-guest QEMU run) and W5-A/B/C (session+throttle,
  payment boundary, channel hub) still in flight.
- merge wave 5 (2026-08-16, orchestrator review): W5-A std.enterprise_session
  (salted-credential login, bearer resolution, insert-only revocation/expiry,
  deterministic fixed-window throttle incl. login brute-force window;
  auth_routes + store_app_handle_bearer; 6/6, red-first on expiry). W5-B
  std.enterprise_payment (provider signature seam, webhook dedupe BEFORE
  transition validation, atomic captured->sale_pay_order same-uow, 3-class
  reconciliation; foundation gains payments role; 7/7, red-first 4/7; honest
  note: nested-BEGIN flattening relied on for same-uow claim). W5-C
  std.enterprise_channel (mode-struct SPI + deterministic mock, cursor
  checkpoints, exactly-once import via chan:<id> idem keys, kill switch,
  reconcile; 9/9, red-first 8/9). W4-A (QEMU in-guest) still in flight.
- merge wave 6a (2026-08-16, orchestrator review): W6-A std.enterprise_hcm
  (effective-dated contracts, attendance intervals, leave w/ overlap conflict,
  payroll BOUNDARY export vs hand-computed oracle; hcm role; 8/8, red-first
  7/8). W6-B std.enterprise_procurement (requisition->approve->PO->partial
  receipts->invoice; receipts write the SAME stock_moves ledger sales read —
  integration case proven: post-receipt sale_place_order succeeds, stock 5->3,
  payable oracle 5000c; 8/8, red-first 7/8; goods_sale regression 7/7).
  FINDING (open): state-dependent feasibility checks ran BEFORE replay
  detection, denying legitimate idempotent replays with insufficient-stock;
  fixed in procurement by asking feasibility only of not-already-recorded
  commands. goods_sale has the SAME latent shape and was deliberately not
  touched (shared path) — queued as its own lane with a spec that must fail
  first. W4-A in-guest QEMU: rung (b) NOT reached, honest deferral. Kernel-tier
  FAT32 rt_file_* facade + OVMF gate rungs L3.5a/b landed; retained transcript
  build/os/ent_store_rung_b_attempt_2026-08-16.serial.log shows in-guest write
  rc=0, fsize=5, open=OK, L3.5b [MISS] on read-back extraction. Two real
  defects fixed: Simple->C `text` ABI is ONE RuntimeString ptr (not ptr+len;
  the wrong-length write masqueraded as disk-full) and a FAT32 per-call
  aligned-buffer leak. Resume: dump first 16 bytes the extraction loop sees.
- merge wave 6b (2026-08-16): W6-C std.enterprise_finance merged. Trial
  balance / AR / AP reads over the EXISTING journal; period close as
  insert-only period_locks with a trial-balance snapshot. SEAM: the period
  check lives in enterprise_store/records.spl (period_latest_close,
  journal_post_allowed, journal_post_pair) — goods_sale.post_journal and
  restaurant.rest_post_journal are thin wrappers, so both inherit the lock
  and the dependency stays finance->store. LIMITS (documented): only
  postings routed through journal_post_pair are checked (a raw
  store_insert_row into journal bypasses it); the lock is a hard freeze
  through a date, not a window; locks are insert-only (no reopen). Two real
  bugs fixed: (1) uow_rollback does NOT undo issued inserts on this backend,
  so a denial inside the UoW left an order_events row and flipped derived
  status — validation now happens BEFORE uow_begin; (2) period-transition
  was checked before idempotency, misreporting a replay as invalid-transition.
  Red-first 4/6 -> 6/6; regressions goods_sale 7/7, restaurant 7/7, booking
  8/8, payment 7/7. Merge fixes by orchestrator: 3-way dropped the finance
  role (base predated wave 6a) — re-added by hand, and the action strings
  corrected from fin.* to finance.* to match the implementation's
  role_allows calls. Merged-tree reruns: finance 6/6, goods_sale 7/7,
  restaurant 7/7.
- HARNESS DEFECT found by W6-C, applies to THIS orchestration (2026-08-16):
  lane worktrees were created with `build` symlinked to the main tree, which
  causes CROSS-WORKTREE COMPILE-CACHE CONTAMINATION — W6-C observed a
  `post_journal` hardcoded to false still producing accepted orders because
  the compiler resolved a CACHED goods_sale from another worktree. Impact:
  red-first evidence produced inside lane worktrees may be unreliable where
  the sabotaged module was cached elsewhere. MITIGATION APPLIED: (a) running
  lanes W7-A/W7-B were told to remove the symlink and re-verify from
  scratch; (b) every merge in this orchestration was re-verified by running
  the specs in the main tree (its own build dir) after merge — those runs
  are the trustworthy evidence, and all have been green; (c) future lane
  worktrees must NOT share build/. Re-verification of earlier lanes'
  red-first claims under clean caches is an OPEN follow-up.
- merge wave 7a (2026-08-16): W7-A goods_sale replay-ordering fix merged.
  Reproduce-first honored: BEFORE any impl change the spec went 7/3 with
  three named red examples — replaying an order that consumed the last stock
  returned insufficient-stock, and replaying pay/refund returned
  invalid-record, all instead of duplicate-key. The pay/refund pair is a
  SECOND instance of the defect (the status-transition guard is itself
  state-dependent on the command's own effect). Fix mirrors procurement:
  feasibility asked only of a not-already-recorded command; state-independent
  checks (shape, unknown sku not-found, unknown order) stay unconditional;
  each new example also asserts a FRESH key is still denied, so the guard is
  not merely disabled. W7-A removed its build symlink and re-ran BOTH red and
  green from scratch, so this evidence is cache-clean. Lane verdicts:
  goods_sale 10/10, store_app 3/3, web_app 5/5, payment 7/7, procurement 8/8,
  restaurant 7/7, booking 8/8. Canonical rule doc added:
  doc/07_guide/app/enterprise/replay_and_state_dependent_validation.md.
  ORCHESTRATOR HAND-MERGE: goods_sale.spl had diverged (W6-C added the
  period-lock seam on main). Merged so that a REPLAY returns its recorded
  result BEFORE the period check — a replay posts nothing, so a closed period
  must not turn a successful replay into invalid-transition. Merged-tree
  reruns: goods_sale 10/10, finance 6/6.
- merge wave 7b (2026-08-16): W7-B conformance sweep merged — THE defect was
  systemic, not local: state-dependent feasibility evaluated before replay
  detection in 14 COMMANDS across 6 MODULES (booking confirm/cancel/no_show;
  restaurant table_open/line_transition/bill_close; payment create_intent;
  hcm hire/terminate/clock_in/clock_out/leave_request/leave_decide;
  proc_requisition_approve). Reproduce-first: conformance spec 3/5 red ->
  8/8 green. Notable: (a) procurement, used as the "reference fix", was only
  HALF fixed — proc_requisition_approve still had the bug, contradicting its
  own docstring; (b) hcm_vertical_spec had the drift BAKED INTO an assertion
  (a step labelled "replay returns duplicate-key" asserted conflict) —
  corrected; (c) session_issue returned invalid-credentials, OUTSIDE the
  documented closed set — legitimised as a deliberate anti-enumeration denial
  rather than weakened. New: foundation.reason_set()/reason_allowed() make
  the closed set an EXECUTABLE predicate, so the conformance spec asserts
  membership by calling it, never by grepping prose; new gate
  test/01_unit/lib/nogc_sync_mut/enterprise_conformance_spec.spl drives real
  commands (no source-text assertions); canonical contract doc
  doc/07_guide/app/enterprise/guarded_command_contract.md with the full
  module x command x invariant matrix. W7-B removed its build symlink BEFORE
  any run, so its counts are cache-clean. ORCHESTRATOR HAND-MERGE:
  restaurant.spl bill_close and foundation.spl both diverged; merged so a
  replay returns its recorded result BEFORE the period check (same rule as
  goods_sale), and exported reason_set/reason_allowed which the lane had left
  unexported (the conformance spec imports them). Merged-tree reruns:
  conformance 8/8, restaurant 7/7, finance 6/6, hcm 8/8, procurement 8/8,
  booking 8/8, payment 7/7.
- merge wave 8c (2026-08-16): W8-C back-office web routes merged — 19 routes
  for HCM / procurement / finance through the EXISTING hardened prelude, plus
  a dashboard roll-up (employees, open POs, payable total, tb-balanced) that
  degrades to 0/empty via store_migration_applied when a vertical's schema is
  absent. Reads gated by the frozen role_allows using existing action strings;
  no new auth scheme or storage. Spec back_office_web_spec 7/7; red-first
  (esc() '<' replacement sabotaged AND the forbidden arm of deny() deleted)
  4/7 with escaping, 403 and roll-up all biting; restored 7/7. Regressions
  store_app 3/3, web_app 5/5, conformance 8/8. Merged-tree reruns: 7/7, 5/5,
  8/8. FINDING (fixed): store-error and invalid-credentials had NO explicit
  arm in web_common.deny and were silently inheriting the 409 default — a 500
  and a 401 presenting as conflicts; every closed-set member now has an
  explicit arm. FINDING (open, escalated not worked around): fin_ap_open
  gates on migration id `proc_001_payables` which NOTHING applies —
  enterprise_procurement applies proc_001_suppliers and books payables into
  the shared journal under accounts_payable, so GET /fin/ap always renders an
  empty line-item list. The route reports the authoritative journal payable
  total alongside it so the page is never silently wrong. Fix = either a
  payables projection in procurement or repointing fin_ap_open at the
  journal; queued as its own lane (W9-A).
- VACUITY AUDIT CLOSED (2026-08-16, lane W8-A): the integrity debt created by
  this orchestration's shared-build/ harness defect is discharged. Under a
  VERIFIED-clean cache (worktree build/ confirmed a real directory), all 7
  audited specs BITE: conformance 8->7 (replay rung undone in one payment
  command), goods_sale 10->6 (journal_post_pair credit +1, unbalanced),
  store_web_harden 4->3 (esc() passthrough), auth_throttle 6->4 (throttle
  always admits), store_harden 5->3 (store_verify always ""), payment 7->6
  (provider_verify always true), booking 8->5 (ranges_overlap always false).
  Every sabotage was applied to the IMPLEMENTATION only, every one was
  reverted, and each spec returned to its original green. Zero non-biting
  specs; no broader fallback sabotage was needed. Conclusion: earlier lanes'
  CONCLUSIONS were sound, only their evidence path was contaminated — that
  path is now closed and future worktrees get a private build/. Table lives
  in doc/07_guide/app/enterprise/guarded_command_contract.md § Vacuity audit.
- IN-GUEST SIMPLEOS PROVEN (2026-08-16, lane W8-B): L3.5b CLOSED. Under real
  OVMF pflash -> GRUB-EFI -> multiboot1 (never -kernel, no isa-debug-exit),
  against an EMPTY mkfs.vfat NVMe volume so every byte read back is one the
  guest wrote, the enterprise store's marker round-trips inside the guest.
  Retained transcript doc/09_report/2026/ent_store_in_guest_ovmf_2026-08-16.serial.log:
    [ent-store-dump] /ENTHEAD.TXT fsize=10 n=10 cbytes: 83 80 76 83 84 79 82 69 49 10 ...
    [ent-store] head read-back=SPLSTORE1
    [ent-store] facade write+read-back=OK
  New gate: scripts/check/check-enterprise-store-in-guest-ovmf.shs.
  ROOT CAUSE (a defect class worth remembering): an `extern fn mmio_read8`
  DECLARED IN A .spl FILE does not bind to the kernel's Simple
  os.kernel.boot.mmio.mmio_read8 — it binds to the C symbol mmio_read8 in
  boot/type_stubs.c whose body is `return NIL_VALUE`. Every extracted byte was
  0. FAT32 was never at fault, which is exactly why write/size/open were green
  while the marker never came back. Read-back moved into C; the permanent
  entstore_fat32_dump_first16 keeps ground truth visible.
  Also landed: W4-A's never-committed C write backing (the 4 guest externs had
  NO C side in main), and a fix for the Rust seed failing to link at all
  (duplicate strong rt_heap_live_bytes/rt_heap_peak_bytes in heap.rs and
  runtime_memtrack.c; core-C shims now weak).
  L4 [MISS], deferred honestly — SAME defect class one layer out:
  file_backend.spl:31 declares its own `extern fn rt_file_exists`, so it exits
  through the C symbol and loses to a freestanding stub instead of reaching the
  facade's @export("C"). Resume: nm which object supplies rt_file_exists, then
  rerun the gate. Merge checks: c-runtime-compiles PASS (120 files), file
  backend spec 6/6.
