# Feature: Secure Pure-Simple Web and Database Servers

## Raw Request

Fresh yolo replacement lane for secure Pure-Simple web and database servers.
Complete the canonical plan with SPipe, parallel agents, guides, and a
higher-capability final review; commit, serialize integration, push to main,
prove reachability, and leave the detached worktree clean.

## Task Type

feature

## Refined Goal

Ship production-reachable Pure-Simple web and database servers that fail closed
on unauthenticated, malformed, oversized, ambiguous, concurrent, and replayed
requests, with durable transaction semantics and retained SPipe evidence.

## Acceptance Criteria

- AC-1: The canonical web entrypoint accepts a real TCP connection and routes it
  through the existing hardened parser, router, response writer, security
  headers, and request-identity path; no benchmark or foreign protocol server
  substitutes for that route.
- AC-2: Web requests enforce bounded request-line, header count/line, body,
  read-iteration, keep-alive, and timeout policy and reject malformed framing,
  conflicting duplicate security headers, unsupported transfer coding, and
  static-file traversal before dispatch.
- AC-3: Production TLS startup rejects missing or invalid certificate/key
  material, never silently downgrades to plaintext, and exposes any explicit
  plaintext development mode in configuration and evidence.
- AC-4: The DB server owns a bounded TCP listener/accept lifecycle, per-
  connection cleanup, explicit shutdown, bounded message/connection capacity,
  and a transport adapter over the existing owned TCP facade.
- AC-5: `OPEN` authenticates a configured principal before capability lookup;
  unknown, missing, and wrong credentials fail identically without exposing or
  logging secrets, and credential checking has no content-mismatch early exit.
- AC-6: Concurrent DB connections have one authoritative mutation owner or an
  explicit synchronization boundary, and readers cannot observe the in-memory
  P3/P4 durability window.
- AC-7: Optimistic conflict tokens survive reopen and a client-provided commit
  identifier is idempotent across retry/reconnect, including the lost-
  acknowledgement case.
- AC-8: Bounded batch and range operations preserve per-table capabilities,
  transaction overlay semantics, deterministic ordering, and response-size
  limits; overflow fails closed without partial application.
- AC-9: Modern SSpec scenarios cover real web routing, request rejection, DB
  authentication, listener cleanup, concurrent visibility, restart conflict,
  idempotent retry, and bounded batch/range behavior with absolute oracles,
  deliberate-red calibration, REQ/AC traceability, and no placeholder pass.
- AC-10: Every changed SSpec has one `sspec-maintain scan` scorecard, a mirrored
  `doc/06_spec` manual with `0 stubs`, and a primary operator flow using the
  shared step vocabulary below; executable specs remain only under `test/`.
- AC-11: The canonical Phase-6 plan, requirements/design references,
  `doc/07_guide/lib/pure_simple_servers.md`, feature/layer expert skills, and
  any discovered unresolved bug records are current. Workflow/skill/command
  trees are N/A because this feature consumes rather than changes SPipe/tooling.
- AC-12: Changed Simple files pass focused check/lint/test, duplication,
  dependency, numbered-artifact, direct-runtime, STUB001, and spec-layout gates;
  release-bound evidence includes the whole interpreter suite once a healthy
  Stage-4 self-hosted CLI is admitted.
- AC-13: A highest-capability reviewer accepts scope, interfaces, security and
  durability semantics, generated-manual quality, exclusions, evidence, and
  done marks before integration.
- AC-14: Intentional changes are committed; under
  `/tmp/simple-main-restart12-push.lock` the lane fetches origin/main, rebases,
  pushes `HEAD:main` with `GH_TOKEN` and `GITHUB_TOKEN` unset, refetches, and
  proves the pushed HEAD reachable from `origin/main` without force or branch.

## Scope Exclusions

- New wire-protocol or TLS implementations when an existing Pure-Simple owner
  already exists.
- Rust/C protocol-server fallbacks, raw-source production launchers, or local
  `rt_*` declarations outside owned provider modules.
- Snapshot isolation beyond the accepted read-committed plus optimistic-
  conflict contract.

## Cooperative Review

- Sidecar WEB owns AC-1..3 and web-focused SSpec evidence.
- Sidecar DB owns AC-4..8 and database-focused SSpec evidence.
- Sidecar DOC owns AC-9..12 documentation, manual, and verification inventory.
- Merge owner: root Codex agent in this detached worktree.
- Final reviewer: a fresh highest-capability Codex reviewer after integration.
- Concrete shared interfaces after cycle-2 DB correction:
  `SecureServerPolicy`, `DbTransport`, `DbListener`, `TcpDbTransport`,
  `TcpDbListener`, `AuthenticatedPrincipal`, `CommitIdentity`, `BoundedQuery`,
  and `DbServerCapsule`.
- Manual flow steps: `Bind the production listener`; `Reject an unsafe web
  request before dispatch`; `Authenticate the database principal`; `Commit and
  recover one durable transaction`; `Retry one commit id without reapplying`;
  `Bound a batch or range response`; `Shut down and release the connection`.
- Setup/checker helpers: `secure_web_server_fixture`, `secure_db_server_fixture`,
  `expect_web_request_rejected`, `expect_db_auth_rejected`,
  `expect_commit_recovery`, `expect_bounded_query`.
- Any not-yet-implemented shared helper must call `fail(...)` or
  `assert(false)`; silent no-ops are forbidden.
- Generated-manual review owner: DOC sidecar, accepted by final reviewer.

## Phase

dev-blocked

## Log

- dev: Created state file with 14 acceptance criteria (type: feature).
- dev: Existing checkpoint `af5dbffaeda` contains unverified DB credential and
  request-bound work; it is input to review, not accepted evidence.
- implement: WEB sidecar added bounded production parsing/listener policy,
  explicit plaintext development mode, fail-closed TLS configuration, and a
  focused scenario/manual. GAP-TLS-3 still blocks production HTTPS reachability.
- implement: DB sidecar added the owned TCP transport/listener, sequential
  state owner, EOF cleanup, durable conflict/commit identities, bounded
  batch/range operations, and focused scenario coverage.
- refactor: DOC and design sidecars added final requirements/NFRs, architecture,
  detail design, test/agent plans, canonical guide/TLDR, and feature/layer
  expert knowledge. Workflow/skill/command updates are N/A because no SPipe or
  verification contract changed.
- merge-owner: corrected auth unknown-principal comparison and prevalidated all
  batch ids before overlay mutation. Runtime evidence remains blocked by the
  unhealthy deployed Stage-4 CLI and root btrfs metadata precondition.
- verify: highest-capability review REJECTED implementation handoff and feature
  completion. Open blockers include unreachable production TLS, missing web
  request identity/security-header flow, distinguishable variable-work DB auth,
  unsafe listener shutdown, principal-unbound replay receipts, non-byte-bounded
  range work, and missing real-listener/runtime evidence. No AC was promoted.
  This is the historical cycle-1 verdict; later source corrections narrow but
  do not erase it, and require fresh review rather than rewriting provenance.
- evidence-followup: Authored deterministic pre-bind invalid-capacity teardown
  coverage over the real `listen` entry point, a capability denial matrix, and
  mirrored manuals for the changed DB durability/tier specs. A proposed
  no-client loopback listener scenario was rejected during root audit: accepting
  any bind error was vacuous, while a shutdown-polling accept may wait forever
  without a concurrent connector. Live bind/accept/client/EOF/stop evidence is
  therefore explicitly RED/BLOCKED pending a concurrent fixture and admitted
  runtime; no listener PASS is claimed.
  Existing durability coverage binds the P3/P4 crash matrix and lost-ack retry
  to fresh-disk and principal-bound receipt oracles. Static review found no
  placeholder assertions in these additions. The unhealthy admitted Stage-4
  CLI still prevents execution, `sspec-maintain`, `spipe-docgen`, runtime
  coverage, socket transcripts, and genuine deliberate-red fail/restore
  provenance; AC-9/10/12/13 remain open and no runtime PASS is claimed. Exact
  inventory: `doc/09_report/secure_pure_simple_servers_evidence_status.md`.
- cycle2-contract-audit: Reconciled architecture/design/guide/plan names with
  post-rebase source. Exact auth-frame equality is asserted for missing, wrong,
  and unknown credentials. Production `serve_tcp` now shares
  `bounded_message_response` with the scripted adapter, structurally closing
  the bypass; runtime TCP evidence remains blocked by CLI admission.
- cycle3-high-review: Highest-capability review again rejected handoff and
  completion, identifying unusable idle-listener shutdown ownership, ignored
  TCP write failure, unbounded web connection spawning, and stale plan prose.
- cycle3-final-fix: Added shared stop control that closes the DB listener,
  propagated transport write status into connection/session cleanup, added
  shared atomic web admission with bounded rejection and guaranteed release,
  and reconciled the plan. Final static gates pass. The three-cycle cap is
  reached; production TLS and admitted runtime/live-socket evidence remain
  blockers, so no AC or ledger row is promoted.
- staged-runtime-provenance: Selected the current-source self-hosted Stage-2
  artifact at `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`, SHA-256
  `5883722a6cafd17006ecab001e714e9e43774014bf44b1af459a92bd142099f5`,
  Build ID `9db2d66edbf77fc3fd0674f3cc21ae4062a2b6ec`. Its producer transcript records
  LLVM/core-c-bootstrap, `SIMPLE_BOOTSTRAP=1`, and
  `SIMPLE_NO_STUB_FALLBACK=1`. The artifact identifies as
  `simple-bootstrap 1.0.0-beta`; an unverified operator observation says its
  `check` and `test` probes returned `unknown command`. It is temporary
  negative/provenance material only, never admitted Stage-4 or AC evidence.
- temporary-seed-diagnostic: User-authorized bootstrap diagnostics observed
  durability 22/0 and, after bounded test-only corrections, secure DB 7/0.
  Tier DB ended 39/1 on UTF-8 batch round-trip after the third attempt, so the
  iteration cap is exhausted. No immutable command receipt or admitted
  Stage-4 runtime exists; these observations promote no AC or ledger row.
- continuation-truth-audit-2026-08-16: The audited baseline was detached HEAD
  `00496db6f95a12dfc7d7c0ecd21648093be61322`, equal to the then-local
  `origin/main`. Later commits in that baseline moved the synchronous parser's
  limit/header policy and route matching into `std.common.net.http_core`, but
  this lane's guide and verification inventory had not been reconciled. Their
  recorded green counts used a runner with a seed-banner caveat and remain
  diagnostic only, not Stage-4 evidence for this lane.
- continuation-code-only-2026-08-16: Bounded sidecars prepared fixes for the
  synchronous `Transfer-Encoding` fail-closed regression, bounded/write-all
  HTTP responses, the DB protocol's UTF-8 byte-slice mismatch, and a real
  loopback DB bind/OPEN/EOF/cleanup/rebind fixture. These are unexecuted
  working-tree changes until the merge owner runs each focused criterion once
  on an admitted Stage-4 self-hosted CLI; they promote no AC.
- continuation-evidence-audit-2026-08-16: AC-9/10/12/13 remain open. Existing
  hand-authored mirrors are not docgen receipts, no current `sspec-maintain`
  scorecards exist, and the secure web scenario's manual-step/boolean-wrapper
  quality findings were corrected only in the unexecuted working spec; a fresh
  scan and generated-manual review are still required before AC-10 can pass.
  The exact deferred command order is authoritative in
  `doc/03_plan/sys_test/secure_pure_simple_servers.md`.
- continuation-review-cycle1-2026-08-16: Fresh highest-capability review
  rejected the first code-only handoff because retained listener-control copies
  could close the same raw fd twice, the idle-stop oracle and canonical DB
  steps were missing, two changed mirrors were stale, and architecture/design
  named a nonexistent `stop_listening` API. Fix cycle 1 added one shared
  mutex-backed close-once authority, a retained-copy idle accept/stop/join/
  rebind scenario, canonical steps/matchers, synchronized the affected manuals,
  and reconciled the lifecycle contract. Re-review and Stage-4 execution remain
  required; no AC is promoted.
- continuation-review-cycle2-2026-08-16: Re-review rejected close-once alone:
  normal close did not publish stopped state to retained copies, and a fixed
  sleep did not prove the worker reached accept. Fix cycle 2 replaces copied
  raw-fd ownership with owner-local listener values plus one shared scalar
  mutex lease/terminal receipt, serializes bounded accept and close, gives the
  stopping domain only `DbStopControl`,
  and requires its accept-attempt receipt before stop/join/rebind. Final
  re-review and Stage-4 execution remain required.
- continuation-review-cycle3-2026-08-16: Final review rejected the remaining
  post-stop accept/dispatch race: stop could be published while bounded accept
  was in flight and a completed connection could still reach authentication or
  mutation dispatch. Fix cycle 3 rechecks stop immediately after accept, closes
  the transport before dispatch, and adds a post-receipt stop/connect oracle
  requiring an empty response and zero accepted/active/session state. The
  three-cycle cap is reached; no PASS is claimed without Stage-4 execution and
  a future independent acceptance review.
- post-rebase-failure-triage-2026-08-16: Mutable `/tmp` diagnostics from an
  explicitly inadmissible Rust-seed run were used only to locate failures, not
  as acceptance evidence. They showed that class-valued mutex payloads became
  nil in three DB listener scenarios, an older DB assertion inspected the
  input instead of returned `ServeOutcome`, and the SimpleOS gate expected a
  retired noalloc allocator path. The working fix uses an owner-local listener
  plus scalar mutex lease/terminal receipt, asserts the returned outcome, and
  verifies the bounded aligned RISC-V bump heap while removing the dead weak
  allocator declaration. Admitted Stage-4 execution remains required; no AC
  is promoted. Independent repair review cycle 1 accepted the scalar listener
  lease, returned-outcome assertion, post-stop dispatch guard, and RISC-V
  bump-heap oracles with no blocking source finding; this is code-review
  evidence only and does not replace either interpreter test.
