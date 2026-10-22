# Checked HIR resource preflight

Executable source: `test/01_unit/compiler/mono/mono_invocation_preflight_v1_spec.spl`.

**12 authored scenarios; execution UNRUN.** This manually maintained companion groups related acceptance cases. Qualified SPipe generation, execution, coverage, native memory/performance and formal verification remain pending. Source review does not establish any of those results.

| Step | Action | Required observation |
|---|---|---|
| Admit retained generic evidence | Visit an open composite function type and effects without specializing it. | Actual preflight returns facts and balances depth; no HIR is mutated. |
| Enforce exact work and depth | Measure actual traversal, retry fresh ledgers at the exact work/depth boundary and one below. | Exact limits succeed; insufficient limits return the specific resource error and restore depth. |
| Bound text and dictionary snapshots | Pass large retained text, empty and populated indexes, and a missing required dictionary declaration. | Text is charged before copying; actual dictionary traversal is bounded; absent required declarations refuse. |
| Include retained defaults | Compare actual generic functions before and after adding a retained default; supply a true flag with no payload. | Default graph contributes measured work; missing required expression refuses. |
| Reject schema drift | Compare actual exported codec, canonical rules and flat-pool versions with changed versions/rules. | Only the pinned version/rules tuple is accepted; no canonical-codec authority is implied. |
| Isolate failure state | Poison one ledger, then create a separate invocation. | Failure stays sticky in its owner; the fresh owner is independent. |
| Refuse absent required function key | Pass an actual function dictionary containing a nil key and a present declaration. | Shape failure returns before looking up the absent key; shared traversal depth returns to zero. |

Remaining acceptance obligation: dictionary snapshot allocation is reserved from cardinality, while the native key provider scans capacity. The accepted total source-work bound remains OPEN until a supported provider scan bound or admitted compact-input mechanism exists; these cases do not prove that bound.
