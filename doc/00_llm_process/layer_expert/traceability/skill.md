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

Sidecar sources (2026-11-06, design slice 3 in
`doc/05_design/app/traceability_cli_sdn_v1.md`): the legacy bug DB is too
large for the capture caps (3.67 MB vs 1 MiB) and its rows cannot be pinned
locators or authorized claims, so `std.common.traceability.legacy_bugs_v1`
parses only the `bugs_active`/`bugs` sections (active wins), `sidecar_v1`
turns rows into labeled `located_in`/`reproducible_by` references, and
`build_snapshot_trace_graph_with_sidecar_v1` binds the source sha into the
input manifest while adding only bug *nodes* to the graph. The app reads the
file through the no-follow byte reader + runtime-backed decode: the std text
codec's interpreted UTF-8 validation costs ~21 s for this file on the seed.
`list bugs --status/--severity/--file-prefix` filter before paging and fold
into `visibility_context`, so cursors bind the filter.
Slice 4 adds `std.common.traceability.annotations_v1` (`# @req` header lines
-> `req:X verified_by <spec>` sidecar rows, authority `annotation-claim`) and
the app scanner `snapshot/spec_annotations_v1` (`--spec-root`, `dir_walk`,
whole-file no-follow reads, one source digest per root). The seed's
`dir_walk` is correct and fast (2,171 specs in 31 ms); the bounded reader
refuses over-bound files instead of truncating, so files are read whole.
