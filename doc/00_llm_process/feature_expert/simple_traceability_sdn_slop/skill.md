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
