# Traceability and Slop development status

The SDN-only trace graph, admission profiles, run reports and Slop viewer are
under development. Proposed commands in the 2026-10-03 report are not yet
verified through a deployed source-matched CLI. Do not use the report as a
command-availability reference or treat an old `traceability: clean` as proof
that the proposed obligations ran.

Start from [requirements](../../02_requirements/feature/simple_traceability_sdn_slop.md),
[architecture](../../04_architecture/simple_traceability_sdn_slop.md),
[detail design](../../05_design/simple_traceability_sdn_slop.md), and the
[complete acceptance plan](../../03_plan/sys_test/simple_traceability_sdn_slop.md).
Current research is in `doc/01_research/{local,domain}/simple_traceability_sdn_slop.md`.
Lane state and retained progress are in `.spipe/simple_traceability_sdn_slop/`.

Authored intent belongs to requirement/SSpec/feature owners; deterministic
conventions supply structural targets. Irregular links carry a reason and one
owner. Actual outcomes remain runner-owned. A linked lower-level test is not
executed merely because an acceptance scenario passed. Source, configuration,
test definition, binary/build input and provenance must match before reuse.

All Simple-owned structured interchange in this feature is SDN. Existing JSON
callers are migration work, not an alternative supported final interface.
Stable structural pages and immutable per-run reports remain separate.

Runtime verification is currently blocked by the absence of an admitted Stage 4
CLI; see [runtime prerequisite](../../08_tracking/bug/traceability_runtime_admission_2026-10-03.md).
The Windows wrapper's Rust fallback is not qualification evidence. Source
implementation continues in parallel, but there are no new runtime PASS claims.
