# Trace and API CLI sketch

Status: proposed UX, not implemented command documentation, 2026-11-01.

```text
simple trace list feature-groups|features|requirement-groups|requirements|bugs
simple trace show <kind> <id> --snapshot=worktree|index|git:<revision>
simple trace walk <id> --direction=outgoing --depth=2 --limit=100
simple trace path <from> <to> --edges=<typed-filter>
simple trace impact <id> --snapshot=index
simple trace gaps <id> --format=sdn
simple trace report <id> --format=md|html --output=<explicit-path>
simple api list|check|violations --snapshot=<subject>
simple api explain <surface-id>
simple api migration-plan <scope> --format=sdn
```

All command names/options are design candidates. `traceability-check` currently
has its own SDN-only parser; P0 must reconcile help without breaking it.
`list`/`show` have table human defaults; SDN is structured default. JSON requires
explicit external interoperability. No implicit report file or network fetch.

```text
Snapshot: git:<resolved-oid>   Graph: complete   Evidence: not run
Kind          ID                 Title                 Coverage
requirement   REQ-TRC-013        Evidence eligibility  definitions linked

Selected: API:module.symbol    Rule: extreme_public_api    DENIED
Exposure: export -> callback return -> Option -> builtin i64
Origin: source span + generated/reexport path    Policy: robust / <digest>
Suggestion: domain-specific nominal type; private storage; typed construction
```

Show authored versus inferred relations, precision, hidden/truncated counts,
provider freshness and source provenance. A migration plan groups by semantic
domain and callers, preserves explicit uncertainty and proposes no automatic
rename or source edit. Diagnostic text explains a concrete path, not only
"avoid primitives". Keyboard users can navigate the same IDs in Slop.

Future CLI captures belong in `build/test-artifacts/<spec-relative-path>/`.
No captures were generated in this design-only change.
