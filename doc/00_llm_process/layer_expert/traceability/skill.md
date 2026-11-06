# Common traceability layer expert

Source owner: `src/lib/common/traceability`. This is a pure shared contract
layer: typed graph/schema, immutable snapshots, resolution, evidence eligibility,
indexes and bounded projection. App adapters own filesystem/Git/network/report
writes. Compiler adapters provide canonical semantic facts; this layer must not
become a second type checker or process/session lifecycle owner.

Preserve v1 readers and historical provenance; page exhaustion is distinct
from graph completeness and qualification. Full graph export must preserve
cross-page edges. Artifact visibility, compiler publicness and caller
authorization are separate concepts. Public record fields alone cannot certify
producer trust or artifact bytes.

Read [architecture](../../../04_architecture/extreme_typing_traceability.md),
[detail design](../../../05_design/extreme_typing_traceability.md) and
[source-gap audit](../../../01_research/local/extreme_typing_traceability.md).
Proposed interfaces remain unimplemented until reviewed runtime evidence says
otherwise. Source work uses the selected feature/layer knowledge receipt.

## Query entry (2026-11-06)

`src/app/traceability/query_main.spl` has a `main`, so it runs directly:
`<simple> run src/app/traceability/query_main.spl list|show <kind> [id]
[--format=sdn] [--snapshot=git:<rev>|index] [--declaration=<sdn>]`. Same args
and exit codes as `simple trace`. Registered declarations may start with `#`
comment lines (the SDN parser now skips leading comment lines for every
top-level shape, not only block mappings). The git/index snapshot routes use
`OwnedProcessLease` and need the native runtime provider; the worktree preview
does not. Agent-facing reading guide: `doc/07_guide/infra/trace_query_p0.md`.
