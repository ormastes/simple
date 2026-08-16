<!-- codex-design -->
# Secure Pure-Simple Servers Agent Task Plan

## Fixed contract before sidecars

Shared interfaces: `SecureServerPolicy`, `ConnectionAdmission`, `DbTransport`,
`DbListener`, `DbListenerControl`, `DbStopControl`,
`AuthenticatedPrincipal`, `CommitIdentity`, `BoundedQuery`.

`std.common.net.http_core` owns the transport-neutral HTTP limits, header/body
policy, path safety, and route matching now consumed by the synchronous server.
That reuse is source structure, not live-listener or production-TLS evidence.

Manual step and fixture/checker names are fixed in
`doc/05_design/secure_pure_simple_servers.md`. Any unfinished helper must call
`fail(...)` or `assert(false)`; a silent placeholder cannot be merged.

## Lanes

| Lane | Ownership | Acceptance scope | Handoff |
|---|---|---|---|
| WEB sidecar | canonical TCP route, bounds, TLS refusal/encrypted flow, web SSpec/manual | AC-1..3, web part of AC-9/10 | Changed paths, one-time results, GAP-TLS-3 status |
| DB sidecar | listener/transport, auth, mutation owner, durable identity/version, bounded queries, DB SSpec/manuals | AC-4..8, DB part of AC-9/10 | Changed paths and independent durability/lifecycle oracles |
| DOC sidecar | links, guide/expert records, manual inventory, static gate inventory | AC-9..12 | Trace matrix, zero-stub/scorecard evidence, blockers |
| Integration owner | reconcile shared interfaces, run nonduplicated gates, commit/rebase/push | AC-12/14 | Commit and reachability proof |
| Final reviewer | fresh highest-capability review | AC-13 | Explicit accept or findings |

Lower-model sidecars: permitted for the bounded WEB, DB, and DOC inventories
after the fixed contract above. Broad findings, generated-manual quality,
exclusions, and done marks require normal/highest-capability review.

## Scope boundary

This is the accepted shortened Phase-6 secure synchronous web/database lane.
It does not mark the broader original
`simpleos_secure_web_db_servers.md` waves for async SSR, pgwire, SSH/PQC,
cross-server performance, or GPU acceleration complete. Those require their
own canonical requirements and executable evidence.

## Merge order and ownership

Merge owner: root Codex agent in this detached worktree. Reconcile shared
interfaces first, then WEB and DB behavior, then DOC evidence. Do not overwrite
unrelated dirty work. The final reviewer is a fresh highest-capability Codex
agent after integration and before delivery integration.

## Blockers and stop conditions

- GAP-TLS-3 (no owned encrypted `TcpStream` overlay) blocks production HTTPS.
- An unhealthy Stage-4 self-hosted CLI blocks runtime acceptance evidence.
- DB listener/stop ownership, sequential synchronization, batch/range logic,
  and Markdown mirrors exist in source. After review cycle 1, retained listener
  controls share one mutex-owned listener state, while the stopping domain
  retains only `DbStopControl`; an idle-stop fixture exercises the accept
  receipt, stop, join, and rebind without a client. A second fixture connects
  after that receipt and stop publication and requires zero dispatch/session
  state. The loopback lifecycle, stop races, and UTF-8 corrections remain
  unexecuted; existence is not independent proof.
- The shared-core extraction regressed synchronous rejection of non-chunked
  `Transfer-Encoding`; the continuation source fix and bounded response writer
  require focused execution before WEB-1/2 can receive credit.
- Existing mirrors are hand-authored and uncredited. Current scorecards,
  docgen receipts, deliberate-red calibration, and operator-manual review are
  still required; the working web-spec quality corrections do not satisfy
  AC-10 until the maintenance and generated-manual gates run.
- Each criterion runs once per session; stop after three fix cycles and report
  WARN rather than looping.

## Delivery

After reviewer acceptance, commit intentional changes. Under
`/tmp/simple-main-restart12-push.lock`, fetch `origin main`, rebase onto
`origin/main`, push `HEAD:main` with `GH_TOKEN` and `GITHUB_TOKEN` unset, fetch
again, and prove HEAD reachable from `origin/main`. Never force-push or create
a branch; require a clean tree before writing the completion marker.
