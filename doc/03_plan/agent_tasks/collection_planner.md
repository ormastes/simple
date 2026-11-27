<!-- codex-design -->
# Collection planner work lanes

## Current implementation checkpoint

The primary owns integration in `C:/dev/simple-item3-dev-20261003` and draft
PR 2285 targeting `release/1.0`. The planner worktree implemented explicit
hash grouping, generic indices and stable hashed uniqueness, then moved to
shared semantic fixtures. The research worktree reviewed registry/driver,
typed-column and index changes and owns the bounded explicit-loop extraction
increment. The spec worktree is frozen at `d53aed4ec74` for canonical Windows
bootstrap after repairing its inherited sparse-checkout layout. Its current
source must not be updated while the bootstrap is active.

All lanes retain their worktree-local ownership receipts. The primary reviews
each source integration; no authored tests, source review or bootstrap launch
is counted as an executed acceptance PASS. Full scope and merge criteria below
remain unchanged.

Scope: REQ-001–011. Merge owner and final reviewer: primary Codex agent at
normal/highest available capability. Research sidecars reviewed compiler,
library and domain evidence on 2026-09-27; none edited files.

| Lane | Ownership | Sidecar |
|---|---|---|
| P0 semantics | closure/functional/Dict parity and five-engine fixtures | N/A for implementation |
| Typed library | Series<T>, DataFrame bridge, numeric edge policy | N/A for implementation |
| Registry and lint | SDN validation, typed facts, COLL diagnostics | N/A for implementation |
| Planner | loop extraction, proofs, physical candidates, MIR lowering | N/A for implementation |
| Profile and perf | `.sprof`, scaling fixtures, thresholds and RSS | N/A for implementation |
| Evidence | executable SPipe, generated manual, verify report | N/A for implementation |

The primary model owns shared interface names and scenario helper names in
`doc/05_design/collection_planner.md` before any implementation sidecar is
assigned. Independent lane outputs require primary review for semantics,
ownership, complexity claims and generated-manual quality before merge.

## 2026-10-03 isolated parallel execution (Codex)

Target integration branch: `release/1.0`; initial base:
`e9cd3153c881c55f59eaaa2573b4b8a5e803023a`; refreshed private research lane
before mutation to `cb2f783acf0ea22e8da54ff0d8d18b4fb14c816c`.
These are work branches based on the release lane, not permission to move the
protected release ref directly or publish a release tag.

| Lane | Isolated worktree / work branch | Owned work and handoff |
|---|---|---|
| Research/design | `C:/dev/simple-item3-research-20261003`; `work/item3-research-20261003` | Append evidence to local/domain research, architecture/detail design and this agent plan; commit only those five files. |
| Acceptance | Parent-assigned isolated spec worktree and branch, recorded in its session receipt | Own canonical system acceptance plan, executable modern SSpec and corresponding manual; stable scenario IDs and honest red/infrastructure evidence. |
| Production | Parent-assigned isolated implementation worktree and branch, recorded in its session receipt | Own production implementation and focused tests; consume shared contracts, record red/green evidence, avoid editing research/spec lane files. |
| Integration/review | Parent-owned isolated integration worktree and branch, recorded in its session receipt | Inspect every lane diff, integrate explicit SHAs, resolve interface conflicts, verify full scope and generated-manual quality, submit reviewed PR to release/1.0. |

Owner: primary Codex integration agent; final review: normal/highest available
capability primary agent. No lower-model finding or done mark is accepted
without that review. Each worktree records its owner/session/path/branch/
target/base/expected target before mutation. Unrelated dirty work is preserved.

Canonical scenario IDs come from `doc/03_plan/sys_test/collection_planner.md`.
The detail design's existing helper names are shared; no lane invents a second
runner, fallback PASS or synthetic executed-plan receipt. Library contracts
and typed planner contracts may progress independently; enabling a compiler
rewrite waits for REQ-002, the relevant key substrate, production lowering and
differential evidence.

Merge checklist: full REQ-001–011 matrix, real five-engine semantic evidence,
selected NFR measurements, runtime and MCP smoke gates, generated manual
quality, no executable specs in doc/06_spec, and no unresolved P0/P1 review
findings. Report remaining gaps explicitly instead of treating an advisory
selector, documentation-only update or focused passing subset as completion.

## Status 2026-10-25 (verified against origin/release/1.0.0 @ 52ecd8b7725)

| Area | Status | Evidence |
|---|---|---|
| Typed registry, checked `typed_series` adapters, guarded advisory planning | DONE (merged) | PR #2285 (`6c905c710c6`), follow-up PR #2304 (`ae932d53f79`), evidence PR #2309 (`abdebaa4360`) |
| CLI policy/budget transport and argument validation | DONE (merged) | `93bc526ff95`, `e1c2cce4157` |
| Builtin collection dispatch identity (`BuiltinCollection` in HIR/codec/type infer) | DONE in source | `src/compiler/20.hir/hir_types.spl`, `generated/hir_codec.spl` on release/1.0.0 |
| MIR consumption of plans | PARTIAL — only guarded literal-membership plans | `97b13f9eb09` (`test/.../mir/collection_literal_membership_spec.spl`) |
| Driver archive/current-body gate preservation | PARTIAL (analysis-only) | `a7b8b4cdcef`, `ba0a687f9e6` (2026-10-12); driver still publishes "analysis snapshots, never lowered/executed receipts" |
| General filter/projection/group/aggregate/join lowering | OPEN | no lowering path beyond literal membership |
| Five-engine semantic equivalence, NFR-001–007 measurements, per-host done gate | OPEN | no executed receipts in `doc/03_plan/evidence/seven_plans/` for item 3 except the 2026-09-29 Windows builtin-identity note |

Host completion for item 3 remains NOT DONE on every host; the advisory
selector is not completion.
