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
