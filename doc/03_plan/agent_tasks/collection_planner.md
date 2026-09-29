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
