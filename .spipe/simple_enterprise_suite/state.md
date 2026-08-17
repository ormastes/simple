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
- merge wave 9a (2026-08-16): W9-A closed the AP silent-wrong-answer defect.
  REPRODUCE-FIRST: before any fix, a new example seeding two real
  purchase-to-stock flows (3x700c + 2x250c) showed fin_ap_open returning 0
  line items and a 0 total, while TWO independent oracles in the same run —
  proc_payable_total and the trial-balance accounts_payable credit — both
  reported 2600c. The money was on the books; the report hid it. Spec 6/8 red
  -> 8/8 green. FIX = journal-derived (option a): fin_ap_open groups the
  tenant's accounts_payable postings by ref and nets credits - debits.
  Rejected a payables projection in procurement because the journal already
  determines the balance — a projection is a second copy that can drift and
  would need its own period-lock story. Bonus properties: a settlement posted
  through records.journal_post_pair clears a line for free (asserted), and any
  FUTURE accounts_payable writer is picked up with no code change. Dead
  proc_001_payables probe removed. NEIGHBOUR AUDIT: fin_ar_open CORRECT
  (derives from order_events + sales_revenue credit); dashboard payable
  roll-up CORRECT (already journal-derived); GET /fin/ap was WRONG by the same
  bug and now asserts line items, not just a total. Web layer simplified: the
  compensating "authoritative journal total" is now the sum of the page's own
  lines (mirroring page_ar) so total and lines can no longer disagree;
  finance_routes no longer imports enterprise_procurement. Regressions all
  green: finance 8/8, procurement 8/8, goods_sale 10/10, back_office_web 7/7,
  conformance 8/8. Merged-tree reruns: finance 8/8, back_office_web 7/7,
  procurement 8/8.
- wave 9b (2026-08-16): W9-B attacked the native-ACID row and returned an
  HONEST NEGATIVE — the row stays blocked, but the blocker is now located and
  mechanised, and the previously recorded resume condition was WRONG.
  Findings: (1) `--mode=native` is the SAME non-ACID emulation — byte-identical
  probe output vs the interpreter (rollback a no-op, UNIQUE unenforced, stale
  count on a freshly deleted db file); it is in-process JIT over
  interpreter_extern/sffi_db.rs. (2) CRITICAL for evidence integrity: the JIT
  SILENTLY DEGRADES on enterprise_store — "[jit-fallback] unresolved external
  symbol 'store_open': whole module dropped to the interpreter" — so a
  --mode=native run of these specs is an interpreter run wearing a native
  label. The lane therefore did NOT run them under that label and relabelled
  nothing. (3) The bug doc's premise that rusqlite is already a seed dependency
  is FALSE (no sqlite in ldd, none in any Cargo.toml) — corrected in place.
  (4) store_backend_acid stays false under both modes; the honest probe holds.
  DELIBERATELY NO atomicity specs: under the emulation both candidate
  assertions are vacuous in the DANGEROUS direction (rollback leaves the row,
  a UNIQUE violation returns success), so they would pass while proving
  nothing. New gate scripts/check/check-sqlite-backend-acid.shs prints
  ACID/NONACID/BLOCKED as its last line and today prints BLOCKED. NOTE: in the
  lane worktree it blocked with `codegen: undefined symbol: rt_sqlite_open`;
  in the main tree it blocks earlier with `runtime archive identity is
  missing/stale: build/simple-core/libsimple_runtime.a`. Both are honest
  BLOCKED states but the main-tree archive staleness masks the real linker
  gap — refresh that archive before treating the undefined-symbol error as
  the current frontier. Prereq for the real fix: add runtime_sqlite.o (or the
  staged provider .so) + -lsqlite3 to the SINGLE-FILE `compile --native` link
  line, reusing is_sqlite_runtime_symbol (native_project/linker.rs:500) which
  the project pipeline already has. Host is otherwise ready (libsqlite3 +
  headers installed; runtime_sqlite.c includes the real header).
- SECURITY AUDIT (2026-08-16, lane W9-D): 12 attacks probed through the real
  dispatcher/commands; 4 SUCCEEDED before fixes. All now fail closed, and the
  successful attacks are retained as regression fences.
  EXPLOITED #5a PAYMENT SIGNATURE LIFT (money bug): the webhook signature
  covered ONLY envelope.payload, so a valid capture signature for intent 1,
  replayed with intent 2's provider_ref and a fresh provider_event_id,
  CAPTURED THE SECOND ORDER AND MARKED IT PAID. Fix: signing material is now
  pwh/v2|tenant|ref|kind|event_id|payload via provider_sign_webhook /
  provider_verify_webhook -> denied invalid-record.
  EXPLOITED #3b SESSION TOKEN DERIVABLE/COLLIDING: token was
  sha256(entropy|tenant|actor|now); two same-second logins produced ONE token,
  and anyone knowing a constant entropy could derive ANY actor's token from
  public inputs. Fix: token also binds server-side secret_hash +
  session_issued_count sequence.
  EXPLOITED #6a UNAUTHENTICATED 20MB LOGIN BODY: body_decision ran only inside
  store_app_handle, so the auth routes — the ONLY unauthenticated surface —
  applied no limit (200). Fix: body_decision is rung 0 of auth_routes -> 413.
  EXPLOITED #6b CREDENTIAL STUFFING: the login throttle keyed on a
  caller-controlled form field, so rotating `user` left /auth/login
  effectively unlimited (40/40 processed). Fix: tenant-wide anon throttle
  charged BEFORE the per-user one -> 429.
  A TEST WAS ENCODING THE VULNERABILITY AS A FEATURE: auth_throttle's "same
  entropy + now yields the same token" asserted the collision as expected
  behaviour. Rewritten (not weakened) to assert two distinct, independently
  resolvable sessions.
  Already safe, kept as fences: tenant isolation (5 read + 3 mutation routes),
  authorization (11 back-office routes vs the sales role), revoked/expired/
  cross-tenant bearer tokens, SQL payloads into prepared binds, XSS on 6
  rendered surfaces, 3 traversal shapes, cross-tenant webhook replay.
  RESIDUAL RISKS (documented in doc/07_guide/app/enterprise/security_posture.md,
  NOT fixed): entropy quality is still caller-supplied; the provider seam is a
  sha256 stand-in (not constant-time, no timestamp tolerance, NOT PCI
  evidence); throttle_count is an unpruned full-table scan (amplification over
  time); role_allows is a hardcoded table whose reads reuse write actions;
  form_value cannot express &/= and does no percent-decoding; /booking/* and
  /restaurant/* reads are authenticated but not role-gated.
  Spec enterprise_security_audit 8/8. Merged-tree reruns: security 8/8,
  payment 7/7, auth_throttle 6/6, conformance 8/8, back_office_web 7/7.
- FULL REGRESSION + WIKI (2026-08-16, lane W9-C): 48/48 spec files GREEN, 429
  examples, 0 failed, 0 dropped, 0 environment-blocked spec rows, 0 timeouts —
  14 unit + 13 system + 21 ubs_test. Gates: cross-OS PASS (8 probes,
  host+simpleos), c-runtime-compiles PASS (102 files). OVMF in-guest gate
  deliberately not run (owned elsewhere, very long).
  STALENESS CAVEAT (orchestrator): that sweep ran against a tree PREDATING the
  W9-A AP fix, W9-B native-ACID docs and W9-D security fixes. It is therefore
  not a current whole-suite number. Coverage is completed by the post-merge
  reruns of every spec those merges touched: finance 8/8, payment 7/7,
  auth_throttle 6/6, conformance 8/8, back_office_web 7/7, security 8/8,
  procurement 8/8, goods_sale 10/10, restaurant 7/7, store_app 3/3,
  web_app 5/5, file_backend 6/6. A fresh single-pass whole-suite sweep on the
  current tip is the next verification item.
  ONE RED, harness plumbing not a regression: ubs_test/restaurant_lane_spec
  reported declared>=1 executed=1 failed=1 timeout=1
  reason=daemon-no-response. The tell is `declared>=1` against the spec's real
  12 examples — the runner never received the daemon's declaration. Standalone
  re-run 12/12 green. Recorded as landmine 9.
  WIKI: doc/00_llm_process/feature_expert/enterprise_suite/skill.md rewritten
  — full module map (store + records period-lock seam + file_backend + faults
  seam + audit_hash, all verticals, all web route families, http_core
  unification, conformance gate), complete verification command list, 5
  environment-blocked rows with resume commands, and 9 landmines including the
  new one that cost two lanes days: a .spl-declared `extern fn` silently binds
  to a same-named C runtime stub (rc=0, plausible fsize, empty read-back —
  presents as a storage bug).
  GUIDE FRESHNESS: audited mechanically (every backticked API identifier in
  doc/07_guide/app/enterprise/*.md and enterprise_store.md resolved against
  the sources) — ZERO drift, no edits needed; store_app.md already documents
  all 41 routes. find doc/06_spec -name '*_spec.spl' | wc -l = 0.
- NATIVE-ACID UNBLOCKED IN SOURCE, NOT YET IN THE DEPLOYED BINARY (2026-08-17,
  lane W10-C). The gate prints `ACID — rollback removed the row, UNIQUE
  violation rejected` (exit 0) ONLY when driven by a LOCALLY REBUILT seed.
  ORCHESTRATOR VERIFICATION in the main tree with the DEPLOYED bin/simple:
  after clearing the stale archive (rm -rf build/simple-core) the gate reaches
  exactly the error the seed edit fixes — `BLOCKED — AOT native build failed:
  error: codegen: undefined symbol: rt_sqlite_open`. So: the source fix is
  landed and correct, the capability requires a seed rebuild + redeploy
  (scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy), and
  until then this row stays BLOCKED for anyone using the deployed binary. Do
  NOT cite the ACID verdict as current repo state without naming the rebuilt
  binary that produced it.
  RULE EXCEPTION, EXPLICITLY FLAGGED: this required editing the RUST SEED
  (linker/native_binary/linker.rs gains object_requires_sqlite, an
  UNDEFINED-symbol test mirroring is_sqlite_runtime_symbol, adding on-demand
  runtime_sqlite.o + -lsqlite3; native_project/tools.rs gains
  build_sqlite_runtime_object) and the C RUNTIME. Justification recorded:
  bin/simple IS the seed, and the pure-Simple linker that already lists
  -lsqlite3 is never reached by `compile --native`, so there is no
  pure-Simple path to the capability. Non-sqlite binaries are unaffected.
  FINDING: src/runtime/runtime_sqlite.c had NEVER ONCE been compiled into a
  linked binary — it tagged integers (v<<3) and returned SPECIAL_TRUE/FALSE
  while sqlite_sffi.spl declares `extern fn -> i64` and codegen passes scalars
  raw. from_int/as_int are now identities; c-runtime-compiles PASS (120 files).
  DISCRIMINATION PROVEN TWICE (the probe is not vacuous): the same probe under
  the interpreter still shows after_rollback_row1=[alpha] and
  dup_insert_ok=true, and CPython's sqlite3 independently confirms a real
  sqlite_autoindex_t_1 with alpha absent and beta present. The script demands
  in_tx_row1=[alpha]/committed_row2=[beta] first and otherwise reports
  `BLOCKED — probe is vacuous`.
  TRAP RECORDED: on the stale-archive failure the compiler SILENTLY FALLS BACK
  TO THE INTERPRETER and still produces output — the lane mistook emulation
  output for native results once. Clear build/simple-core before trusting any
  native run.
  RETRACTION: W9-B read `start_count=48` as evidence of a global emulation
  counter. It was ASCII '0' — sqlite_count does int(count_str) on a RUNTIME
  string and returns the ASCII of the first digit (0->48, 1->49), while
  int("142") on a literal is correct. That reading is withdrawn; the
  underlying non-ACID conclusion stands on the other evidence.
  REFINED BLOCKED ROW (next frontier): store_backend_acid returns false EVEN
  NATIVELY, one layer above sqlite. Standalone every primitive is right
  (before=[0], begin, insert, mid=[1], rollback, after=[0]) yet store_open()
  reports acid=false with is_file=false. Suspect the pragma/CREATE/marker-write
  state established just before the in-situ probe. Next diagnostic spelled out
  in the guide and bug doc.
- L4 CLOSED — FULL ENTERPRISE STORE RUNS IN-GUEST ON SIMPLEOS (2026-08-17,
  lane W10-B, one fix/verify cycle of a permitted three). Gate now
  `PASS — 6 rung(s) checked, enterprise store read its own marker in-guest`;
  L1/L2/L3/L3.5a/L3.5b/L4 all [OK]. Transcript
  doc/09_report/2026/ent_store_in_guest_ovmf_l4_2026-08-17.serial.log:
    [ent-store] open=OK / insert=OK / count=2 OK
    enterprise store open=true verify=[] (file-backend, in-guest FAT32)
  Interleaved [ent-store-c] write len= 10 -> 32 -> 53 shows the file genuinely
  growing as rows append, so the count is not a constant.
  DIAGNOSIS (static, via nm, before booting): TWO INDEPENDENT DEFECTS STACKED,
  which is why any single-cause fix would have failed.
  (1) LINK ORDER: the freestanding link passes `-z muldefs`
  (linker.rs:2289/2298), so a Simple @export("C") and a same-named C stub are
  BOTH STRONG and do not collide — first in link order silently wins, and boot
  C objects precede Simple module objects. @export does keep its unmangled
  name (mangle.rs:202), so the facade genuinely competed and lost. Losers:
  NOP1(rt_file_exists) in rt_extras.c returning NIL_VALUE (every existence
  probe answered "no" -> open=FAIL) and TRAP_STUB_RET(rt_file_size,1), which
  WOULD HAVE HALTED THE CPU had fb_open reached it.
  (2) ABI — the half that makes "just weaken the stubs" wrong:
  rt_file_exists/rt_file_size are in codegen's text_arg_indices, so every call
  site lowers rt_file_exists(p) -> rt_file_exists(rt_string_data(p),
  rt_string_len(p)), a raw (ptr,len) pair. A Simple provider taking one boxed
  RuntimeValue CANNOT be correct even after winning the link. The other two
  symbols are not in that table and pass boxed values.
  FIX, split by symbol at its own layer: real rt_file_exists/rt_file_size in
  baremetal_stubs.c over the FAT32 API with the (ptr,len) signature their call
  sites emit; both competing stubs DELETED (each replaced by a comment on why
  nothing may re-add them); facade declares those two as extern. Post-fix nm
  shows exactly ONE definition per name — no longer link-order dependent.
  file_backend.spl DELIBERATELY UNCHANGED: its local externs were never the
  bug and the recorded ?-TryOperator/standalone-SMF reason still holds.
  Merged-tree verification: c-runtime-compiles PASS (120 files), cross-OS PASS
  (8 probes), file_backend spec 6/6.
- FRESH WHOLE-SUITE SWEEP ON TIP (2026-08-17, lane W10-A): 49/49 spec files
  GREEN — 439 executed, 439 passed, 0 failed, 0 dropped, 0 timeouts, 0
  environment-blocked, ~33 min, one spec per process, verdicts read from
  SPEC FILE VERDICT. Landmine 9 did NOT recur (restaurant_lane declared>=12
  executed=12 passed=12). This supersedes the stale 48/48 number. Gates:
  cross-OS PASS (8 probes), c-runtime-compiles PASS (102 files), sqlite-acid
  BLOCKED — and note this lane hit the REAL `undefined symbol: rt_sqlite_open`
  form rather than the main tree's stale-runtime-archive form, confirming the
  archive staleness is a local artifact that masks the true frontier.
- COVERAGE HOLE FOUND (open, needs an owner): the recorded suite is
  SELF-SELECTED and has never included 21 `*/http_server/*_spec.spl` files
  present on disk. Swept separately: 12/21 green, 9 RED — 168 examples, 131
  passed, 37 FAILED. These predate this round's merges and are not caused by
  them, but "the suite is green" has been true only of the subset someone
  chose to list.
  (a) THREE ARE ORPHANED AGAINST AN API THAT DOES NOT EXIST:
  lib/http_server/{security_headers 7/0, rate_limit 6/0, request_validation
  11/0} all die with `semantic: function default_security_headers_config /
  default_rate_limit_config not found`, and `grep -rn` over src/ returns ZERO
  definitions of either. They test a surface that was never written or was
  removed without them.
  (b) SIX ASSERTION REDS: nogc_async_mut/http_server/compression 19/11
  (`expected gzip to equal lz4`), protocol_handler 8/7,
  static_compression_cache 8/7, range_numeric_guard 1/0 (both copies),
  security_context_dispatch 6/5.
  Next action: a dedicated lane must triage each — decide per spec whether the
  IMPLEMENTATION is missing/wrong (fix it) or the SPEC is stale against a
  deliberately removed API (delete it with justification) — and then FOLD ALL
  21 INTO THE RECORDED SUITE so the enumeration can never silently drift
  again. Deleting a spec merely because it is red is not acceptable.
- DUPLICATE SHA-256 PINNED (2026-08-17, lane W12-C). New parity spec
  test/01_unit/.../enterprise_store_audit_hash_parity_spec.spl — 14/14. The
  oracle is EXTERNAL reference digests (FIPS 180-4 + python3 hashlib), NOT
  mutual agreement between the two implementations: mutual agreement would be
  satisfied by two identically-wrong copies. Vectors: empty, "abc", the FIPS
  56-byte two-block case, 55/56 (classic padding off-by-one), 63/64/65 (block
  boundary both sides plus exact fit), 119/120, a 1000-byte sixteen-block
  input, high-bit-set UTF-8 (would catch a sign-extending u8->i64 in
  ah_padded_byte), and a realistic audit-record JSON. Both implementations
  matched ground truth on all 13 — no drift, no live bug.
  ROOT FIX ASSESSED AND DELIBERATELY DECLINED, with the evidence that makes it
  a trap: rejection sites are in the RUST SEED —
  compiler_rust/compiler/src/compilability.rs:529 (Expr::Slice ->
  CollectionOps) and :879 (Expr::ArrayRepeat -> CollectionLiteral), diagnostic
  at pipeline/execution.rs:266-292 fired from :611/:746; the .spl mirror
  src/compiler/80.driver/compilability.spl is a port with NO callers. Lowering
  exists for both (rt_slice, rt_array_repeat — single calls, no loop emitter),
  and the Dict arm at :555-576 is precedent for relaxing one. BUT the halves
  differ in maturity: rt_slice is threaded into the standalone
  symbol-emission path at four sites in codegen/common_backend.rs (:141, :385,
  :583, :3290) plus elf_utils.rs:601, while rt_array_repeat appears in EXACTLY
  ONE file (codegen/runtime_sffi.rs:267) and is absent from both — so relaxing
  :879 today would LINK-FAIL on an unresolved symbol. Sequenced as its own
  compiler lane: wire rt_array_repeat into the allowlist -> relax :879 then
  :529 with tests -> rebuild seed -> only then collapse audit_hash to a
  re-export. The parity spec survives that collapse, becoming a tautology on
  one side, which is the correct end state.
  Duplication made safe meanwhile: reciprocal DUPLICATE-OF: headers in
  audit_hash.spl and common/crypto/sha256.spl, each naming the other, the
  parity spec, and the rejection-site file:line. Verdicts: parity 14/14,
  enterprise_store 10/10, harden 5/5, cross-OS PASS (8 probes), docgen 0 stubs.
  Merged-tree reruns: parity 14/14, enterprise_store 10/10.
- THREE "ORPHANED" SPECS RESOLVED — THEY WERE NEVER-RUN MIS-AUTHORED SPECS,
  NOT ORPHANS (2026-08-17, lane W11-A). Determination (B) for all three, on
  decisive evidence: `git log -S default_security_headers_config -- src/`
  returns ZERO commits (same for default_rate_limit_config,
  validate_request_path, default_max_uri_length). The commits mentioning those
  names touch ONLY the spec files, and cfe0506e336b added each spec AND its
  implementation module IN THE SAME COMMIT — the impl shipped a CLASS-based
  API while the spec was written against a FREE-FUNCTION API that was never
  written. So nothing was removed; these specs never ran and never could.
  Implementing the named symbols would have been exactly the trap
  (inventing an API to satisfy a test, then stubbing config to clear a load
  error). NO src/lib CHANGE WAS NEEDED OR MADE — the implementations were
  correct all along; only the specs were wrong.
  Repointed to the real API: security_headers -> SecurityHeadersConfig
  .default()/.relaxed(), collect_security_headers, build_hsts_value,
  apply_security_headers (9/9); rate_limit -> RateLimitConfig.default()
  (field requests_per_window, NOT max_requests), RateLimitStore.new(),
  rate_limit_handler (7/7); request_validation -> request_validation_handler,
  contains_null_byte, MAX_URI_SIZE (12/12). Examples now drive the real server
  path — emitted (name,value) header pairs, PreRead Error(429) on bucket
  exhaustion, Read-phase Error(400) on traversal/null-byte/oversize URI —
  rather than asserting on config fields. RateLimitConfig has no `enabled`
  field, so that claim was re-expressed as "default config has no exempt paths
  and no trusted proxies -> the limiter applies to every request and cannot be
  bypassed via X-Forwarded-For".
  Sabotage proof: X-Content-Type-Options emitting "sniff" -> 3/9 red;
  `available <= 0` weakened to `< 0` -> 1/7 red; is_path_traversal branch
  disabled -> 3/12 red; all restored to green.
  Note: these specs import bare std.http_server.*, which resolves to
  nogc_async_mut/http_server (NOT the sync tier the brief assumed). The
  test/unit/ mirrors were byte-identical, so both trees were updated in
  lockstep and the test-tree divergence baseline is unchanged.
  Merged-tree reruns: 9/9, 7/7, 12/12.
- ROOT CAUSE OF THE NATIVE-ACID FRONTIER: SQL STRINGS WERE NOT NUL-TERMINATED
  (2026-08-17, lane W12-A). src/runtime/runtime_sqlite.c's get_string()
  returned rt_string_data() DIRECTLY to sqlite3_exec/sqlite3_prepare_v2, but
  Simple's rt_string is (data, len) with NO NUL terminator — so sqlite read on
  into adjacent heap bytes on every statement. Values from an AOT --native
  stage-by-stage fixture that revealed it:
    A begin=false    err=[near "BEGINX": syntax error]
    B rollback=false err=[near "ROLLBACK<heap garbage>": syntax error]
    C begin=false    err=[cannot start a transaction within a transaction]
    A insert=true mid=[0]   <- the in-tx INSERT was invisible too
    pragmas=true/false/true <- busy_timeout silently failing
  Success depended purely on the byte after the allocation, which is exactly
  why the standalone sequence looked correct while store_open() failed. It
  CASCADES: a rejected ROLLBACK leaves the transaction open, so every later
  BEGIN fails. THE PROBE WAS RIGHT ALL ALONG — probe_backend_acid() honestly
  returned false, and no flag was forced. W10-C's suspects (WAL pragma,
  CREATEs, marker write, unfinalized statement) were ALL WRONG.
  FIX at the C runtime layer only: get_string -> borrow_string/release_string
  copying rt_string_len bytes into a NUL-terminated buffer (128B inline,
  malloc beyond) at all five call sites. No Simple, seed or store.spl change.
  DISCRIMINATION PROVEN: reverting ONLY runtime_sqlite.c makes the new gate
  report `BLOCKED — probe is vacuous: 0 of 8 stages showed the in-transaction
  insert` — i.e. the naive pre-fix reading would have been a FALSE acid=true.
  New gate scripts/check/check-store-open-acid.shs + fixture:
  `PASS — 8 stage(s) checked, probe_backend_acid true at every stage`
  (:memory: and file x 4 cumulative stages), driven by a locally built seed
  (bin/release/** was never touched). check-sqlite-backend-acid probe fields:
  in_tx=[alpha] after_rollback=[] dup=false committed=[beta] rejected=[] =ACID.
  New gated spec in harden: "rolls back a multi-row transaction with zero
  survivors when the backend is ACID" asserts a DEFINITE count on both
  branches (0 when acid, exactly 2 under the emulation) so it cannot pass by
  skipping. Interpreter verdicts: harden 6/6 (was 5), enterprise_store 10/10,
  goods_sale 10/10; c-runtime-compiles PASS. Merged-tree: PASS (120 files),
  harden 6/6.
  HONEST GAP FILED, NOT HIDDEN: store_backend_acid still cannot be READ from a
  native binary — importing std.enterprise_store fails with `undefined symbol:
  rt_file_atomic_write` (from file_backend.spl). The symbol is defined in
  runtime_native.c and present in the only build/*.a; adding a RuntimeFuncSpec
  did not help and was REVERTED rather than left in unverified. Filed:
  doc/08_tracking/bug/native_link_missing_rt_file_atomic_write_2026-08-17.md.
  Under the interpreter the flag stays false, correctly.
- NATIVE-LINK GAP CLOSED: store_backend_acid READS true FROM AN AOT-NATIVE
  BINARY (2026-08-17, lane W13-A). W12-A's `undefined symbol:
  rt_file_atomic_write` was NOT the archive they inspected: with
  SIMPLE_LINKER_DEBUG=1 the single-file --native link line is
  `-L <seed cargo>/release/deps -Bstatic -lsimple_runtime` — the RUST
  runtime staticlib (find_runtime_library_path_for_target prefers exe_dir/deps
  over build/simple-core), and `nm -g --defined-only` on that archive showed
  `T rt_file_write_text_at` x3 but ZERO rt_file_atomic_write. The C archive
  W12-A nm'd (build/simple-core, from runtime_native.c) has the symbol but is
  never on the link line when the seed runs from a cargo tree. Not
  gc-sections, not ordering, not mangling — wrong archive, missing symbol.
  FIX (Rust seed edit, flagged: the symbol must live in the Rust runtime crate
  the link actually resolves against; no pure-Simple layer can add a symbol to
  that archive): rt_file_atomic_write implemented in
  src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs mirroring the C
  semantics (parent-dir create, unix mode preserve, temp+fsync+rename, 1/0).
  RESULT: AOT-native probe importing std.enterprise_store links, runs, and
  prints store_open_ok=true store_acid=true against real sqlite (W12-A's
  NUL-termination fix holding natively).
  GATE EXTENDED: check-store-open-acid.shs stage 2 AOT-compiles
  test/fixture/enterprise_store/store_native_acid_probe.spl and requires
  store_acid=true; now `PASS — 9 stage(s) checked ... native
  store_backend_acid=true`. DISCRIMINATION PROVEN: objcopy-stripping
  rt_file_atomic_write from the linked archive makes the gate report `FAIL —
  native store link stage: error: codegen: undefined symbol:
  rt_file_atomic_write` (the exact original error); restored -> PASS.
  Native codegen limitation observed and worked around in the fixture:
  "{}".format fails at runtime (`Function 'str.format' not found`) in AOT
  binaries — probe prints fixed strings instead.
  Interpreter regression: enterprise_store 10/10, harden 6/6;
  c-runtime-compiles PASS (102 files). Driven by locally built seed
  (/mnt/data/tmp .../release/simple, 59450240 bytes; bin/release/** untouched).
- RESIDUAL SECURITY RISKS CLOSED (2026-08-17, lane W12-B).
  RISK 1 throttle amplification: throttle_admit now sweeps before deciding and
  on the reject path; throttle_prune drops the counter table once EVERY
  retained row belongs to an elapsed window; throttle_rows_retained is the
  absolute oracle — after 900 admits across 300 windows, retained <= 6.
  RED EVIDENCE IS ITSELF THE FINDING: with the sweep removed the spec NEVER
  FINISHES and was killed at 900s — that is the amplification. Sweep made
  unconditional -> 10 passed / 2 failed.
  RISK 2 form_value: percent_decode does one pass, +->space, %XX->byte, and
  FAILS CLOSED on truncated/non-hex/%00; form_value splits on the first = only.
  12-row parsing table specced, plus a hostile case proving an encoded
  <script> is now decoded to its real value AND still rendered &lt;script&gt;
  — the escaping specs were not weakened. Red: naive parser restored ->
  10 passed / 2 failed.
  RISK 3 role-gating — W9-D's "deliberate customer-facing posture" DID NOT
  SURVIVE INSPECTION, and this is a real authorization finding, not a
  consistency tidy-up: there is no customer role and no per-customer scoping,
  so "customer-facing" meant EVERY role in the tenant. A `sales` session could
  enumerate the resource inventory, probe any booking id, and walk table ids to
  read every open bill — lines, quantities, modifiers, totals — with no
  ownership proof. Both families now re-check the frozen role_allows with their
  own action (booking.hold, restaurant.table.open) -> 403 through the existing
  deny() mapping. Red: gates forced open -> 11 passed / 1 failed.
  SEED DEFECT FOUND EN ROUTE, FILED NOT WORKED AROUND SILENTLY: the Rust seed's
  interpreter SQLite emulation parses `DELETE FROM <t>` and CLEARS THE WHOLE
  TABLE, ignoring any WHERE — measured, `DELETE FROM t WHERE 1=0` removed both
  rows and returned success, while the C runtime on real libsqlite3 honours
  WHERE. One statement, two behaviours.
  doc/08_tracking/bug/seed_sqlite_emulation_ignores_delete_where_2026-08-17.md.
  Consequence: the store exposes only store_truncate, and the throttle
  evaluates its predicate in pure Simple first — no conditional DELETE exists
  anywhere in the suite.
  ORCHESTRATOR NOTE: the lane reported enterprise_conformance_spec as
  "does not exist at this tip" and correctly declined to fake a verdict. Its
  search was wrong — the file exists in main and on disk. I ran it on the
  merged tree: 8/8. Also enterprise_web_app 5/5 and security_audit re-run.
  Lane verdicts: security_audit 12/12 (was 9 examples), auth_throttle 6/6,
  back_office_web 7/7, enterprise_web_app 5/5, store_app 3/3.
  REMAINING RESIDUAL (rewritten in security_posture.md): role_allows is still a
  hardcoded table — this made the app CONSISTENT, not finer-grained (no role
  gets "read the bill" without "open a table"); no CSRF/cookie flow; the
  throttle is bounded but still a linear scan of the live window; the sweep is
  all-or-nothing (a consequence of the seed DELETE defect — it can only cost
  boundedness, never weaken a limit); percent_decode decodes BYTES not
  characters; and no route role-gates a WRITE, because that authority lives in
  the guarded commands by design.
- SIX "STALE SPEC" REDS WERE THREE REAL DEFECTS (2026-08-17, lane W11-B).
  (A) security_context_dispatch — A SECURITY BUG:
  validate_remote_security_token_with_adapters did `val active = session`
  after a nil guard, but a plain rebind does NOT narrow
  RemoteSecuritySession?, so every field read raised "unknown property
  'user_id' on Option", the function ABORTED, and the session/token
  user-binding check NEVER RAN — adapter-backed auth silently degraded to
  anonymous. Fixed with `session!`. 5/1 -> 6/6.
  (A) protocol_handler — AN EARLIER LANE'S DISMISSAL WAS WRONG. That lane
  recorded the failure as "a pre-existing string-vs-integer mismatch in the
  spec's own case". Re-derived by bisecting with probe specs:
  build_alpn_extension_block is correct (11 bytes, right framing), but
  wire_to_bytes returned a list of the right LENGTH whose elements are
  one-character TEXT, not integers — the declared [i64] was a lie from
  delegating to generic to_bytes. The impl even carried a comment calling the
  helper "NOT usable", i.e. the caller had been worked around instead of the
  bug fixed. Rewrote it as the true inverse of bytes_to_wire. 7/1 -> 8/8.
  (A)+(B) compression — A FULLY UNCOMPRESSED BODY WAS BEING SERVED. Measured
  every codec on a 300-byte payload: br 304, gzip 42, deflate 28, zstd 310,
  lz4 36. zstd_compress_frame is a CONTAINER WRITER THAT NEVER COMPRESSES, so
  the size guard correctly refused it — but compress_response_for negotiated
  exactly ONE codec and gave up on refusal, so `Accept-Encoding: zstd, lz4`
  served an uncompressed body despite lz4 being offered. Fixed to walk
  preference order to the first codec that actually shrinks (gzip,lz4 and
  lz4,gzip both still pick gzip). Stored-only encoders FILED, not absorbed:
  doc/08_tracking/bug/zstd_brotli_encoders_are_stored_only_2026-08-17.md.
  (B) half: the spec predated br/gzip/deflate being wired and its
  application/octet-stream fixture tripped the MIME allowlist BEFORE
  negotiation was reached — three examples failed for an unrelated reason and
  one passed vacuously. 11/8 -> 20/20.
  (B) static_compression_cache — implementation was RIGHT; the LRU example
  probed both entries then asserted eviction order ignoring its own second
  probe. 7/1 -> 8/8.
  (B) range_numeric_guard — THREE copies and they are NOT duplicates: same
  shape, but each targets a different family's utilities.spl (gc_async_mut,
  nogc_async_mut, nogc_sync_mut). The sync one was already corrected earlier;
  the other two still demanded the dead `to_int() ?? 0` spelling back. 0/1 ->
  3/3 each.
  Sabotage, 6 of 6 green->red->green: compression 16/4, protocol_handler 7/1,
  security 5/1, LRU 5/3, range async 1/2, range gc 1/2.
  Lane sweep: 12 specs, 140 examples, 140 passed. HARNESS CAVEAT RECORDED:
  under load avg 20-27, three runs were SIGTERM'd producing NO VERDICT LINE —
  a missing verdict is NOT a pass, and those were re-run to completion.
  Merged-tree reruns: compression 20/20, static_compression_cache 8/8,
  range_numeric_guard 3/3, async_dynamic_dispatch 6/6, http_core 23/23.

- W13-C (2026-08-17, done): residual-risk closure pass 2 + guarded-command gap
  check. Rust seed 59536728B 2026-08-16, interpreter mode, one spec/run,
  SIMPLE_TIMEOUT_SECONDS=900.
  (1) Entropy: audited every issuer — only spec callers supply entropy; no
  production constant-entropy path exists. Added defensive boundary:
  session_issue denies entropy < session_entropy_min_len() (8 bytes) with the
  generic invalid-credentials. New audit-spec scenario; short spec-only
  entropies in enterprise_auth_throttle_spec lengthened. Sabotage (check
  reverted): 12/1 -> restored 13/0.
  (2) percent_decode multi-byte: verified SAFE — 2- and 3-byte UTF-8 escapes
  decode byte-wise (documented mojibake) but all sequence bytes >= 0x80, so no
  '<'/'>'/quote can appear from inside a sequence; %3C after a multi-byte
  value still escapes via esc(). NO XSS. Fences assert exact decoded byte
  lengths — a first absence-only fence survived a byte-dropping sabotage and
  was strengthened. Sabotage (drop bytes >= 0x80): 12/1 -> restored 13/0.
  (3) Gap check: sale_refund_order (vs seeded PAID order) and proc_receive
  (vs seeded open PO) added to conformance tenancy scenario — 17 denials, all
  invalid-session, fingerprint identical; no cross-tenant mutation. Sabotage
  (session_valid tenant rung forced open): 7/1 -> restored 8/8.
  Regression: audit 13/13, auth_throttle 6/6, conformance 8/8, back_office
  7/7, store_app 3/3. Posture doc updated: residual 1 closed, residual 7
  narrowed to normalisation-only; remainder renumbered 1-7.

- W14-A (2026-08-17) — output-escaping + security-header completeness audit.
  Reproduce-first sweep of every HTML interpolation across booking/restaurant/
  dashboard/auth/hcm/procurement/finance _routes + web_common. Conclusion:
  ALREADY HARDENED (like W13-C). Every request-/store-derived value passes
  through esc(); esc() escapes " -> &quot; and ' -> &#39; so it is
  attribute-context safe (all attrs double-quoted); every response path —
  including deny()/command_page/404/auth-error — is wrapped by secured().
  The one non-esc() interpolation (auth "token=" + r.detail) is a server-
  issued session token, not attacker-influenceable — safe by source.
  Gaps closed were UNTESTED not UNSAFE: attribute context and the vertical
  route families had no fence (prior fence covered only element context on
  /store/catalog via the dispatcher). Added
  test/03_system/app/enterprise/enterprise_output_escaping_audit_spec.spl
  (declared>=5 executed=5 passed=5). Red-first: disabling the " -> &quot;
  replace in esc() flips 3/5 red (attr-context assertions + booking breakout),
  restored 5/5. Audit list: doc/01_research/app/enterprise/
  w14a_output_escaping_audit_2026-08-17.md; posture doc W14-A section added.
  Evidence: Rust seed bin/release/x86_64-unknown-linux-gnu/simple (59536728
  bytes, 2026-08-16), interpreter mode, SIMPLE_TIMEOUT_SECONDS=900.
