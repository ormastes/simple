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

## Current source integration on release_phase3

The draft source now routes `traceability-check --snapshot=index` and
`--snapshot=git:<revision>` through the Git object adapter, extractor and shared
resolver. Supply explicit repository-relative paths. The source recognizes
`--declarations=<path>` for an owned SDN input within those selected paths. The
local preview policy has no authored declaration authorities, so semantic claims
remain unresolved until a registered policy owner admits them. This is source
integration, not verified availability in a deployed binary.

The response retains selected roots, exact subject and content-derived input
identity, with `admission_eligible=false` and `qualification=unverified`. It is
complete only within the selected scope. `--profile=commit`, `push`, `remote`
and `audit` currently fail explicitly; no hook or remote gate may treat this
preview as an admission receipt. The structural input identity excludes its
containing tree; the separate generation identity binds the candidate subject.

Opt-in framework events use `SIMPLE_TRACE_CASE_EVENTS=1`. The runner persists
observed data through its existing DB child before document generation and
reports missing, partial or cached transport as incomplete. These events are
unverified history. The DB owner now accepts strict run requests, allocates
and saves immutable intent, and reloads that intent before acknowledging it.
The internal child operation is `--prepare-request=<SDN file>`; result
submission uses `--trace-run=<allocated ID>` to reconcile against that plan.
These are authored source interfaces, not commands qualified in a deployed
Phase 3 binary. The parent has not yet integrated preparation before dispatch.
Build/config/input provenance and required run reports remain incomplete.

Preparation acknowledgements use `simple.trace.run-preparation/v1` SDN and
bind the exact canonical request, allocated run ID and persisted plan. They
remain unverified intent and cannot qualify evidence. A consumer must reject
nonzero exits, missing or malformed output, mismatched digests and extra output
instead of extracting a convenient acknowledgement from noisy text. Selected
file inventories must match planned paths exactly and satisfy byte/count bounds.
This structural check does not prove semantic case discovery.

Development intent is authored in
`doc/08_tracking/trace/features/simple_traceability_sdn_slop.sdn`: all 20
requirements and 40 planned criteria, with explicit current artifact links.
It contains no execution records. Native parser admission and registered
authority remain pending; file presence is not traceability qualification.
