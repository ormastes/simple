# Repeated materialization root resolution

Status: focused optimization verified; production materializer adoption pending.

The Windows efc724 materializer authenticated 141,525 tracked blobs in 513.7 s.
Its archive-member, omission, transform-repair and alias containment checks each
resolve the same exclusively owned root again. Child resolution must remain:
lexical containment would accept directory-junction escapes.

`scripts/bootstrap/materialization-path-boundary.py` caches only the canonical
root. It resolves every child and checks the root's filesystem identity before
publication. It does not authenticate contents, admit source snapshots, grant
alias authority, or support concurrently mutable roots. The existing exclusive
writer contract remains mandatory; the final identity check is additional
detection, not a substitute for that contract.

## Measured scope

Five alternating process-isolated pairs, each using the same first 2,000 paths
from the authenticated efc inventory, produced identical acceptance digests.
Baseline p50/p95: 1.2691/1.3010 s. Candidate: 0.7150/0.7359 s, a 43.4% p95
reduction for these containment checks. Peak working set: 20,656,128 versus
20,676,608 bytes (20 KiB difference). These figures do not establish a 43.4%
end-to-end materialization improvement. Extraction, hashing and publication
were deliberately not repeated. Five-sample p95 is the maximum sample.

The paired benchmark emits raw measurements, path acceptance digest, Python,
helper and inventory SHA-256 pins. The Windows evidence packet is
`materialization-boundary-paired-perf.json`. Four correctness checks cover
Unicode/normalization, prefix and parent escapes, child junction escapes and
root replacement. A separate 10,000-path streaming check bounds retained and
peak Python allocations; this is distinct from process peak working set.

## Next materializer integration

Copy and pin this helper in a new, unlaunched materialization packet. Construct
`MaterializationBoundary(root)` after validating the exclusively owned root.
Replace `path.resolve().is_relative_to(root.resolve())` with
`boundary.contains(path)`, and likewise use `boundary.contains(destination)`
for alias containment. Call `boundary.verify_root()` immediately before writing
`source-ready.json`. Retain all existing `.git`, Git blob, alias, inventory,
case-collision, archive and physical-input checks. Bind the helper's SHA-256 in
the preparation request. Never modify an already frozen materializer.

Qualification of that integrated successor, including its existing physical
blob proof and final receipt, remains required. No full compiler rebuild is
needed to validate this Python bootstrap-glue change.
