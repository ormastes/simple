# Simple source entity-edit draft adapter V1

This implements a bounded source proposal slice of the selected SCV solver
gateway plan, sections 6–8, especially SCVN-S02. It extends the public library
adapter; no production command, editor-save hook, plugin loader, worker,
publisher, or BuildRunner is integrated by this change.

## Accepted scope and caller

The existing `solve_source_v1` calls `source_merge_v1`: exact equal/unchanged
bytes and independently admitted file moves. The only current callers are
executable specifications and their fixtures. `solve_simple_source_v1` adds
the explicitly selected `source.simple` domain. The accepted host policy must
select `scv.parser.raw-bytes.v1`, `scv.model.simple-entity-edits.v1`, and
`scv.solver.simple-entity-edits.v1`. These labels describe the built-in
interfaces; they are not executing-artifact attestations or installable pins.

`SourceSimpleMergeInputV1` retains the original `SourceMergeInputV1` and an
ordered array of `SourceEntityEditV1`. Each edit binds operation/producer,
FileUid/EntityUid, immutable base and side revisions, identity-map revision,
base byte range, expected base-slice SHA-256, and exact replacement bytes.
The accepted policy binds the complete moves-plus-edits digest, all three
source-file digests, configuration/profile/routing and identity-map revision.
The caller must obtain verified identity/range operations from its admitted
operation owner. A producer string alone cannot verify identity or authorize
an edit. There is no declaration-name, current-path, or similarity fallback.

## Behavior and conservative refusals

1. Account bounded inputs before hashing, then check accepted policy and exact
   immutable read bindings.
2. Reuse file identity/kind/mode and every move precondition from the byte
   adapter. A moved side's digest includes its actual edited bytes.
3. Require regular `.spl` inputs under the accepted semantic route. The suffix
   is a compatibility check after routing, never the authority to select it.
4. With no entity operations, retain the existing exact equal/unchanged byte
   rules. Two distinct concurrent byte changes remain a conflict.
5. Validate all edit identities, revisions, ranges and base-slice hashes;
   reject duplicate operation IDs across moves and edits. All entity IDs must
   be distinct within this conservative V1 transaction, including two edits
   on the same side. Same-entity concurrent changes remain explicit conflicts.
6. Reject overlapping ranges. Adjacent nonempty replacements are allowed;
   an insertion on either boundary of another edit is refused. Two insertions
   at the same point never gain an order from producer traversal.
7. Replay each side independently from the base, in ascending base positions.
   The entire reconstructed byte array must equal its frozen side. Unrecorded
   edits, stale mappings and unused operations cannot silently enter a draft.
8. Replay the combined disjoint edits and retain the evidenced destination
   path. Candidate revision binds every source digest, the complete operation
   bundle and identity-map revision.

The adapter does not parse a function, prove that an EntityUid describes a
particular declaration, infer a refactor, or make a semantic-equivalence claim.
The executable fixture uses two independently identified Simple functions
whose bodies change from `1`/`2` to `10`/`20`.

## Validation and preservation

The host requires ten independent checks: exact input binding, expected
authority state, accepted-policy authorization, executing-provider artifact,
exact byte reconstruction, file identity/operation binding, language parse,
compiler configuration, impacted dependencies, and required tests. Missing
validators remain explicit `unavailable:source.simple:<check>` requirements.

All successful drafts and typed conflicts keep the existing host's
`needs_inputs`, `unqualified-builtin-execution`,
`external-validation-required`, `complete_proposal=false`, and empty admitted
deterministic cache key. An input-binding key is not an admitted provider
result key. The adapter grants no validation or publication authority.

Original inputs are returned on every outcome. Invalid source, empty bytes,
NUL and literal conflict-marker strings are preserved; independent validators
decide promotion. Ordinary filesystem saves/private checkpoints remain outside
this pure API and cannot be prevented or overwritten by it.

## Bounds and evidence

The host caps edits and moves at 128 each and precharges operation comparisons,
text/replacement bytes, repeated replay/hash copying, and base traversal using
the existing conservative budget (64 accounting units per charged item and a
16 MiB ceiling). Selection uses a boolean presence array and quadratic
comparisons, not repeated linear membership scans. Repeated reconstruction is
bounded by operation count times total retained/output bytes. These counters
are deterministic accounting, not measured RSS or a native sandbox.

Tests were authored and committed first in `ad4c1a215c1`; implementation
followed. No admitted `bin/release/<triple>/simple` exists in the isolated lane
or shared checkout. Native SSpec execution, red/green runtime evidence,
coverage, SPipe docgen/maintain, core/MCP checks, and measured latency/RSS are
`not_run`. No Rust seed or BuildRunner substitute is used. Manual and static
review cannot upgrade this to production verification PASS.

Merge owner: parent SCV solver task. Final source/manual reviewer:
`solver_guide`. Sidecars: N/A for this bounded adapter.
