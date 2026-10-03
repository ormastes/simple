# Item 6 precise semantic routing source handoff

Owner: item6_research. Branch: `work/item6-precise-routing-20261003`.
Base: `43f626850b6a5531e89110f75cd1eaedc24adcd1`, target `release/1.0`.
Isolated worktree: `C:/dev/simple-item6-research-20261003`.

The driver now calls `package_index_route_admitted_current_v1`, which derives
per-module semantic changes from admitted old/new graph bytes. The old public
wrapper retains its explicit classification parameter for compatibility; normal
driver requests no longer trust an environment public/private flag.

`package_index_transition_stage_v1` runs inside the existing publisher lock.
It stages a versioned, content-addressed transition embedding the previous
generation and binding the next generation digest, then atomically updates
TRANSITION before CURRENT. The route checks both digests, decodes/validates the
old graph and compares producer/root/variant/scope and topology. Missing,
corrupt, crash-mismatched or incompatible evidence falls back to conservative
public propagation of requested roots. Old index files are not retention roots
because their complete bytes are embedded. Revisiting a digest writes a fresh
pair receipt; idempotent publication does not replace the predecessor.

For nonempty valid hints, all actual semantic graph differences are included,
even when omitted from the hints. Unproven extra hints propagate conservatively.
Malformed nonempty hints fail driver admission. An empty hint denotes no new
event work: do not replay the last completed publication. Existing exact SCV
revision/tree/inventory admission prevents an unindexed source edit from using
an old generation; a newly published graph already binds its typed outputs.

The real source-route fixture exposed a pre-existing mismatch: cold producers
store logical source identities while the dirty-record path owner requires
canonical physical paths. Routing now validates logical inventory paths and
projects them under the admitted snapshot before the existing canonical,
no-follow path checks. No recursive discovery or source parsing is introduced.

## Verification status

Source implementation and 12 explicit SSpec examples are present in
`test/01_unit/compiler/cache/package_index_route_semantic_transition_spec.spl`.
They include mixed edits, omitted roots, cutoff, each semantic dimension,
malformed hints, missing/corrupt/crash-mismatched evidence, predecessor revisit,
collected old index, compatibility changes, and actual archive/source routing.
Dimension loops exercise additional cases. All assertions invoke production
owners; no receipt-string-only system harness was added.

Tests are UNEXECUTED. No admitted pure-Simple runner was available; no Rust seed
was used. Source work is not RED/GREEN evidence. Native compiler/lib/MCP/LSP
checks and paired latency/RSS cohorts remain required by integration.

The actual dirty-source path owner currently rejects non-POSIX hosts with
`unsupported-host`; consequently the real route example explicitly names POSIX
and will expose that existing blocker on Windows. The narrow generation and
invalidation examples do not depend on that source-path owner. Windows source
route qualification remains OPEN rather than silently skipping the assertion.

Normal transition replacement retires the prior pointed receipt. An interrupted
writer may leave an unreferenced immutable receipt, as other staged CAS writes
can; explicit orphan maintenance remains needed. One receipt embeds up to the
existing 256 MiB graph bound. Extra publication memory and elapsed cost have not
been measured; no end-to-end performance or bounded-total-disk claim is made.
Receipt read/retirement races can only remove optional precision and fall back
conservatively; they cannot authorize a stale artifact.
