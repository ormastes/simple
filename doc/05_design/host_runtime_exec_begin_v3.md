# Signed exec child begin and one-use delegation

The sole Host owner retains both Host capacity and Common Container owners.
`host_runtime_exec_begin_v3(local, packet, context, refresh)` returns the updated
local owner, an optional first-begin lease, optional native control cleanup,
recovery state and an error. It never creates an exec session, releases parent
capacity, accepts caller policy bytes or decodes an admission/native capability.

The read-only historical parent validator is shared with capacity reopen. The
child-only wrapper still checks its exact WAL and archived packet first. Before
new admission the producer additionally requires the live journal revision,
current continuity and exact active parent charge. It verifies the child SDK
grant and approval before the native resolver, retains that resolver's returned
owner on every outcome, and checks its exact running parent. The completed
protected installation loader supplies the original signed installation request
and policy. No public Installed struct supplied by a caller is accepted.

The actual Common Container control probe verifies current native parent and
installed control identity. Its updated Container owner and optional cleanup
are returned even when it fails. Authority is refreshed and fully verified
after that probe. The child baseline provider identity remains separate from
the exec-control composite identity; neither is rewritten to match the other.

Shared private publication stages complete bounded bytes, reads them back,
refreshes authority at its no-replace boundary, and retains ambiguous stage
evidence. The exact canonical child packet is archived before admission. An
existing admitted child may resume only with the same archive, no delegation
and freshly verified authority. Executing, outcome-unknown or terminal children
never yield another lease. No child outcome frees or duplicates the parent row.

After the one journal begin, sequence and commit revision are captured before
any other commit. A canonical delegation carries those actual values, the full
signed child packet, full signed installation packet, installed artifact digest,
actual control observation digest/time and raw exec admission deadline. Its
expiry is exactly the minimum of verified child grant and approval expiries;
the parent launch grant's old expiry does not constrain it. The admission's
execution proof digest is the canonical delegation digest, without a cycle.

Only confirmed NEW durable delegation publication permits a returned lease.
Existing, conflicting, ambiguous or failed publication returns no lease and
requires recovery. Every post-begin failure retains the child journal state;
reopen or a second call cannot mint another lease. The provider must still make
its independent exclusive claim and re-probe before actual native exec creation.

This synchronous producer contains native read-only resolver/probe operations.
It is not a gateway callback or proof of priority control responsiveness. Actual
service integration must use the root-approved reserved native process jobs,
with parent-only journal writes and serialized commits. No native effect or
compiler campaign is authorized for this source checkpoint.

Incomplete lifecycle dependency: an already known native exec birth can be
inspected after the original grant expires, but native start requires fresh
explicit authorization for the same intent/envelope. This first-begin API
refuses changed-proof executing/unknown replay and never silently re-creates.
A future resume-start proof consumer must archive fresh proof separately,
bound to the original operation and known birth. It is not implemented here.
No expiry automatically kills a process or releases capacity.
