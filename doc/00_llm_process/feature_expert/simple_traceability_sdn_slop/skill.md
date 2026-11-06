# Traceability, SDN evidence and Slop

This feature is under development. Start with the selected requirements,
architecture and detailed design named `simple_traceability_sdn_slop` and the
same-named system-test plan. The 2026-10-03 report is a proposal/audit, not proof
that commands are available. Read `.spipe/simple_traceability_sdn_slop/state.md`
for actual execution and delivery status.

The pure owner is `std.common.traceability`; app adapters own immutable source
snapshots, processes and publication. `RunnerTestDb` remains the observation
writer. Slop consumes the same graph and eligibility as CLI/Markdown/HTML.
Use the shared canonical SDN codec and reject duplicate issues; never use the
lossy legacy renderer or emit JSON under an SDN extension. Existing codec
limitations require explicit round-trip tests.

Conventional links are structural targets, not execution or semantic coverage.
Missing, not-run, stale, failed and eligible-pass states stay distinct. Candidate
data cannot grant its own producer trust. Stable pages do not carry unpinned
latest PASS or their own containing-tree digest. Source views pin snapshot/blob.

Full scope remains REQ-TRC-001..020, AC-TRC-001..040 plus self-traceability
development criteria. No narrowing to in-memory comparator or source-presence
tests proves the full feature. Use production SSpec paths and retained real
observations, admitted pure-Simple binaries, and explicit host prerequisites.

Current source seams: `app.traceability.extract.snapshot_pipeline` builds scoped
graphs with content-derived manifests; `app.traceability.snapshot_preview`
exposes unverified local inspection through the existing checker entry point.
`std.common.traceability.run_plan` reconciles actual events against separately
frozen intent, while `std.nogc_sync_mut.test_runner.trace_transport` checks missing
per-file carriers. Runner persistence precedes docgen. None of these source
changes has native execution evidence yet. Persistent pre-dispatch plans,
provenance admission, complete reports and trusted gates remain open.

## Querying features / requirements / bugs today (2026-11-06)

The P0 query runs on any `simple` that can `run`, seed included, from the
repository root -- no Stage4 CLI, no build:

```sh
D:/dev/wt/seed/simple.exe run src/app/traceability/query_main.spl list features 2>/dev/null
D:/dev/wt/seed/simple.exe run src/app/traceability/query_main.spl show requirement req:REQ-TRC-001 --format=sdn 2>/dev/null
```

Arguments are the words after `simple trace`; a leading `trace` word is also
accepted. Exit 0 = rendered over a complete graph (normal; still unverified /
admission-ineligible). Authority for the canonical declaration's claims comes
from the policy-owned registry `trace_query_registered_authorities_v1`
(`src/app/traceability/snapshot/query_scope_v1.spl`); a
`TRACE-AUTHORITY-CONFLICT` (exit 1) now means a claim outside that registry,
and a new registered declaration needs its own registry rows. Spec:
`test/03_system/app/traceability/feature/trace_query_authority_spec.spl`. Scope is the registered declaration only (`list bugs` is empty
by design until legacy DB ingestion lands). Full output key reference and the
spec driver (`scripts/check/check-trace-query-p0.shs`):
`doc/07_guide/infra/trace_query_p0.md` § "Running it today on the seed".

`refs requirement req:REQ-TRC-001` (or `refs feature <id>`) lists every authored
claim from/to the identity with the other endpoint's declared file paths; see
the guide's "Reverse references" subsection for how to read `authority`.
