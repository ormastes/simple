# Agent tasks: Web iframe Draw IR embedding

Status: design landed; lane 1 awaits a fresh bounded docgen/runtime session

Frozen names:

- `draw_ir_embed_composition`
- `_simple_web_layout_compose_document`
- displayed SSpec steps/matrix names in the detail design
- unimplemented initial checkers use `fail(...)`

| Order | Lane | Scope | Dependency |
|---:|---|---|---|
| 1 | TDD owner | Modern SSpec/manual with basic/order/clip fail-fast controls | Runtime pending accounting landed in `7220a9aa51ef`; regenerate in a fresh session because the prior iframe docgen lane reached its three-cycle cap and Stage2 docgen still segfaults |
| 2 | Draw IR transform | Rebase offsets/IDs/clips and preserve every other command field | lane 1 |
| 3 | Web producer | Shared composer, depth/rules/deadline child insertion, and ordered child material-witness folding | lanes 1–2 |
| 4 | Engine2D evidence | Existing executor closes frozen pixel matrix | lane 3 |
| 5 | Caller migration | Five callers in frozen order; delete blit helpers last | lane 4 |
| 6 | Traceability/manual | Claim bounded support only after qualified run; zero-stub manual | lane 5 |

Parallel sidecars: `N/A` for lanes 2–5 because they share flat ordering and the
renderer owner. One read-only SSpec/manual reviewer may run beside lane 4 after
the names above are fixed.

Merge owner: primary web-browser hardening agent.

Final reviewer: normal/highest-capability agent at the merged revision. Reject
iframe IMAGE commands, `[u32]` child buffers, lost present-zero clips,
appended-out-of-order children, parent-only material evidence, external `src`
authority, or unqualified PASS.

Stop after three focused verify/fix cycles. Any parity mismatch blocks the
next migration. Any need for full bootstrap, Rust seed, new IR schema, or a
private Engine2D path stops the tranche with a concrete blocker.

## Sandboxed child authority prerequisite (RED)

This is a prerequisite for enabling iframe script, request/navigation, or
input, not permission to enable any of them from renderer recursion.

| Order | Lane | Scope | Dependency |
|---:|---|---|---|
| 1 | Child context owner | Typed child identity, URL/base/Origin, iframe+CSP sandbox intersection, worker mirror | canonical Draw IR child composition |
| 2 | Isolated host owner | `HostedBrowserRendererProcess` child ledger, frozen `SBCI1`/`SBCP1`, separate outer SBR2 and inner one-use permit | lane 1 |
| 3 | Direct host owner | `HostedWebContentSession` through the shared session broker, local permit, no SBR2 wire | lane 1 |
| 4 | TDD/manual owner | Frozen four-step scenario, rejection-before-mutation matrix, hosted/isolated parity, mirrored manual | lanes 1-3; admitted focused runner/docgen |

Parallel sidecars: lanes 2 and 3 may proceed after lane 1 freezes the shared
typed intent/permit interfaces; lane 4 begins after both. Merge owner: primary
web-browser hardening agent. Final reviewer: normal/highest-capability reviewer,
rejecting a worker-owned ledger, ambient child network facade, parent/chrome
access, child-visible permit, stale identity admission, false direct-mode SBR2
claim, or conflated process/DOM/frame generation.

GO: architecture handoff only. Remaining before any production support claim:
real iframe sandbox-token parsing/intersection, child semantic/runtime mirror,
host-ledger issuance/consume/retire, shared direct broker parity, the frozen
executable scenario/docgen, and a focused admitted pure-Simple run. No
bootstrap or Rust seed is authorized.
