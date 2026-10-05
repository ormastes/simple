# Repeated materialization root resolution

Status: focused optimization and successor caller verified on a tiny Git fixture;
next full candidate materialization pending.

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

## Successor materializer integration

`scripts/bootstrap/materialize-source-packet.py` is the parameterized successor
of the efc packet's actual materializer. All four containment sites use the
boundary helper. It retains the `.git`, Git blob, alias, inventory,
case-collision, archive and physical-input checks, including preservation of
transformed archive originals. It verifies root identity immediately before
writing `source-ready.json`; failure prevents publication.

Copy the caller and helper together into a new packet. Prepare `request.json`
with schema `bootstrap-materialization-request-v1` and fields `source_root`,
`repository`, `source_head`, `archive_source_head`, `archive_path`,
`archive_sha256`, and `boundary_helper_sha256`. Use absolute filesystem paths
and full Git commit IDs. The candidate must already be an exclusively owned
worktree with its index initialized to its pinned HEAD and no extracted files.
Invoke the pinned caller with `--config request.json --config-sha256 SHA256`.
The outer launcher must pin the caller itself. The caller checks configuration,
archive and helper hashes, executes exactly the verified helper bytes, and
records all three code/request pins in its final receipt. Running Python with
assertions disabled is rejected. Never modify an already frozen materializer.

Five caller checks passed: real archive authentication and receipt pins;
helper tampering rejected before execution; archive hash mismatch rejected;
root replacement at the final publication boundary rejected without a ready
record; and archive reuse restoring a new blob while preserving and repairing
changed/CRLF-transformed originals. These are tiny authenticated Git fixtures,
not another full source extraction or compiler build. The 10,000-path memory
test measured 964,183 traced peak bytes; its 2 MiB budget applies to that fixture
only, since CPython pathlib's process-wide interning is included.

Qualification of that integrated successor, including its existing physical
blob proof and final receipt, remains required. No full compiler rebuild is
needed to validate this Python bootstrap-glue change.
