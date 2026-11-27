# Simple source entity-edit drafts

**Evidence:** authored manual mirroring
`test/03_system/app/scv/feature/scv_solver_simple_v1_spec.spl`.
Native execution and SPipe generation/maintain are **not_run** because an
admitted runtime is unavailable. This manual describes test assertions;
it does not report passing executions.

Freeze a regular Simple source file with `alpha` returning `1` and `beta`
returning `2`. Retain the exact base and two side revisions. An accepted editor
operation changes only `alpha` to return `10` on the left; a separately
identified operation changes only `beta` to return `20` on the right.

Submit the immutable source models and admitted entity operations to
`solve_simple_source_v1` under the separately accepted `source.simple` policy.
The proposed bytes contain both edits. The original base and both sides remain
available. The result remains a draft requiring independent parse/compiler/
dependency/test and policy checks; missing validators are explicitly unavailable.

The authored scenarios cover:

| Operation or adversary | Expected assertion |
|---|---|
| Independent function body edits | Exact combined bytes, ten required checks, unqualified draft |
| Verified file move plus both edits | Original FileUid and evidenced destination path |
| No entity edits, unchanged left | Exact right-side bytes |
| Empty right with unchanged left | Empty draft preserved, no parse claim |
| Same entity on both sides | `SIMPLE_ENTITY_CONFLICT` |
| Unrecorded trailing source edit | `SIMPLE_SIDE_RECONSTRUCTION` |
| Duplicate edit/edit or move/edit ID | `SIMPLE_DUPLICATE_OPERATION` |
| Stale revision/map/base digest | `SIMPLE_EDIT_PRECONDITION` |
| Negative or overlapping range | Precondition or `SIMPLE_RANGE_CONFLICT` |
| Two insertions at one boundary | `SIMPLE_RANGE_CONFLICT` |
| Operation changed after accepted binding | Failed request without candidate |
| Missing/stale moved-side evidence | `SOURCE_MOVE_EVIDENCE_REQUIRED` |
| Reversed disjoint operation traversal | Same output bytes; distinct ordered-bundle binding |
| More than 128 edits | Resource refusal before payload hashing |
| Incompatible source suffix | `SIMPLE_PROFILE_MISMATCH` |
| Invalid syntax, NUL and literal marker bytes | Bytes retained; external validation required |
| Cancelled or insufficient budget | Explicit cancellation/resource refusal |

This is a public library proposal adapter. The scenarios do not exercise a
production CLI, installed plugin artifact, editor-save hook, publication,
native process isolation, or compiler-backed semantic refactoring.
