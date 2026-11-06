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

Exit 1 = rendered, unverified (normal). The `TRACE-AUTHORITY-CONFLICT` lines
are expected. Scope is the registered declaration plus, since 2026-11-06, the
legacy bug DB as a read-only **sidecar** (`doc/08_tracking/bug/bug_db.sdn`,
2,687 rows, bug nodes + status/severity/file attributes, no graph claims):

```sh
S=D:/dev/wt/seed/simple.exe
$S run src/app/traceability/query_main.spl list bugs --status=open --severity=P1 --file-prefix=src/compiler/ 2>/dev/null
$S run src/app/traceability/query_main.spl show bug bug:<db-id> --format=sdn 2>/dev/null   # legacy: {...}
$S run src/app/traceability/query_main.spl refs bug bug:<db-id> 2>/dev/null               # SIDECAR located_in / reproducible_by rows
$S run src/app/traceability/query_main.spl list features --bug-db=none 2>/dev/null        # declaration only
```

Full output key reference and the spec driver
(`scripts/check/check-trace-query-p0.shs`):
`doc/07_guide/infra/trace_query_p0.md` § "Running it today on the seed" and
§ "Legacy bug DB sidecar".

`refs requirement req:REQ-TRC-001` (or `refs feature <id>`) lists every authored
claim from/to the identity with the other endpoint's declared file paths; see
the guide's "Reverse references" subsection for how to read `authority`.
