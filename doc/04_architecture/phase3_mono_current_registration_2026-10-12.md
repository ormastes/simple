# Complete current-body mono registration mechanics

The unresolved archive remains `lowered-unresolved-v1`. Mono registration
after the real post-HIR transformations must use the complete current body,
not retain the original declaration facts or pretend the archive stage changed.

`MonoArchiveCurrentBodyV1` records the original parent, current artifact/body
and ordered warning digests, `post-hir-resolved-v1`, and parent boundary key/digest.
The shared raw artifact owner stores a length-prefixed frame containing the
exact original module name/path/key/body/warnings, parent boundary, full HIR
codec blob and ordered warnings. The key binds the whole frame and parent
boundary. Borrowed reads require real scope state 1, exact producer, original
parent admission, complete frame consumption, stable re-encoding, full body
identity and ordered warnings. Neither descriptor nor mechanical frame proves
that the production weaver/resolver or preceding validators ran.

`mono_archive_current_registration_create_v1` creates a separate fresh compact
registration state. `mono_archive_collect_current_registration_in_owned_scope_v1`
uses one shared existing collector body: declared globals before generic
collection, all 21 typed row families, canonical template signatures/recipes,
ascending nongeneric root symbols, real counters and cross-module collision
effects. Current receipts carry their current body and predecessor digest;
they cannot be passed as a typed receipt to the original archive publisher.
The parent scope must promote the complete receipt before closing scratch.

`mono_archive_publish_current_registration_v1` opens its own lease, rereads
the complete current artifact and reruns that same collector, validating the
supplied rows against independently recollected rows before any owner changes.
It closes scratch before using the one shared row installer. Current body
descriptors and compact rows are retained; decoded modules, workers, full
functions, executable defaults and symbol tables are not promoted. The current
descriptor schedule is bound to the actual compact predecessor and registration
order. Injecting unresolved registration into the inner state invalidates the
current descriptor coverage/predecessor check.
The prospective compact successor is assembled and hashed inside scratch;
only its digest and root-schedule digest escape. Nonempty owner and current
descriptor digest operations require scope state 1, so source/runtime reads
and serializations of growing compact tables do not allocate permanent
temporary copies at each publication. No cloned successor maps are promoted.

The mechanical transaction is not a final repository factory or production
admission token. Driver prerequisite admission must independently replay the
actual validators, weave, cold capture and configured quiet-resolution step,
pin this exact current frame and order, then authorize its use. Mono root/FIFO,
assembly and verification-use readers still require adaptation to current-body
authority before full activation. The retained production route stays active.

The `current-registration` native fixture uses real parsed/lowered complete
functions, moves which function is generic and which is a root, changes the
return signature and body and adds an executable parameter default. It checks
retained-collector signature/recipe/root/counter parity, original-reader refusal,
full current codec reload, warning order, stage/body/boundary mismatches, altered
root receipt refusal before mutation, actual epoch writeback, repeated receipt
refusal, occupied/paused scopes and post-close replay after 4096 allocations.
Its boundary values are explicitly synthetic mechanical controls, not asserted
production prerequisite receipts. The existing launcher still requires an
actually admitted compiler/runtime capsule and frozen source/fixture snapshots.

Validation is source-only. The 13-check native fixture has not run. There is no
full bounded route, original HIR reclamation, native PASS, timing or RSS claim.
