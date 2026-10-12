# Applied mono publication ledger proof

Review of complete-module assembly found that its execution owner checked root
record names, targets and coverage, but did not capture which complete publication
was actually applied. A genuine same-input/same-target publication from another
base state could replace a completed root record while new coverage was computed
from the replacement. Existing specialization emitted-function digests also did
not bind the complete specialization delta/container record.

The actual root/FIFO consumers now capture a rolling publication seal before
application and install it only after successful actual `mono_archive_apply_v1`.
The seal binds exact ordered root/FIFO kind, complete output archive key (covering
input/output bodies, function identity, target, stage, delta and function record),
and prior captured seal. Every extension validates the complete delta digest and
function/container keys. Preflight recomputes the actual root-prefix/FIFO sequence
inside scratch and compares it with the captured owner seal. Missing interior
roots, out-of-order/base-epoch substitution and any record payload alteration
refuse before further publication, completion, assembly or candidate creation.

The ledger is metadata only. Encoding/recalculation stays inside owned scopes,
and capture promotes only one digest. No input HIR, complete function, worker,
verification owner or full cumulative ledger is promoted. Scope or promotion
failure retains existing fail-closed behavior.

A native negative control is appended in the candidate fixture follow-up: two
genuinely produced stored receipts have the same input archive and target but
different base epochs. Replacing the completed applied root with the other
receipt must refuse completion/assembly without changing the epoch or diagnostic
sequence. Restoring the exact applied receipt must restore valid completion.
That fixture is authored, not executed. Static source checks and guards are not
native writeback evidence or full CLI memory qualification.
