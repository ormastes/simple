<!-- codex-design -->
# Collection planner work lanes

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
