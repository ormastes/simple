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
- Shared interfaces: `SecureServerPolicy`, `DbTransport`, `DbListener`,
  `AuthenticatedPrincipal`, `CommitIdentity`, `BoundedQuery`.
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
