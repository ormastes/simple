# Podman Engine exec ownership and recovery

Status: implementation in progress; executable Simple specifications and live
Podman acceptance have not run. This extends the shared Simple Container API's
Linux Podman provider, using its existing durable file and local Unix owners.
This slice uses detached exec control with explicit numeric user, literal
environment and working directory. TTY, stdin, geometry, secret references and
exec output transport remain separate capabilities and are refused here.

## Admission

The host loads the completed signed control installation from its protected
journal and verifies a distinct signed child exec request. A caller-supplied
socket policy or successful read-only control probe does not authorize exec.
The original host intent binds the parent assignment and operation, original
CLI provider identity, separately observed installed control identity, and the
exact shared exec request. Operation payload and native deadline digests remain
in their existing separate domains: signed intent and raw exec request.

The provider must independently match the exact parent runtime, retained request,
installed policy and observed peer before submitting an effect. Reconnection
cannot silently change the enrolled service identity. Launch expiry governs
request submission, not the subsequent lifetime of the exec process.
The current Host first-begin producer does not renew an executing or unknown
operation. Starting a retained birth after its original grant expires remains
unsupported until an explicit resume-start authorization consumer exists. That
consumer must archive fresh proofs for the same original intent and operation,
without rewriting the original packet or repeating begin/create. Known-ID
read-only inspection does not require renewal.

## Durable state

Journal keys bind actual scope and child operation ID. Nonce and request digest
are immutable record contents, not alternative keys that permit the same
operation to create another exec. Corrupt, unknown-version or changed payload
records refuse effects and remain retained.

The provider publishes create-armed state before any create request byte. A
failure with submitted or uncertain bytes remains unknown; it cannot retry
create, invent an exec ID, or search by helper PID. A received exact native exec
ID and canonical birth evidence must be durable before start is armed. Once an
ID is known, reconciliation inspects that exact ID and never repeats create.
An inspected not-running state alone does not establish that exec ever started
or completed, since the same shape can describe a newly created exec.

Existing file locking, bounded no-follow reads, no-clobber first publication,
atomic replacement and directory synchronization remain the persistence owners.
No second journal framework or native handle registry is introduced. Filesystem
barriers are not a claim of hard wall-time latency or arbitrary power-loss
qualification.

## Parent continuations and copied values

Each continuation performs at most one bounded native Unix IO operation. The
small step deadline is distinct from the total monotonic transport deadline and
the verified Unix submission expiry. A step timeout is pending only while the
total deadline still permits progress. It never means EOF, successful exec, or
permission to reconnect and resend the request.

An offset, partial response, connection owner and pending action remain with the
parent. An operation lifetime claim uses the existing generation-bearing file
lock owner and survives between continuations. A second begin cannot take over
while the first owns a distinct connection. Any retained create record refuses
another create attempt. Copies of language values do not confer another right to send bytes.
The durable revision must be checked and an IO-armed transition committed before
native work; stale revisions refuse work. A restarted IO-armed record requires
reconciliation and cannot reconstruct an old native connection from serialized
metadata. Cleanup errors preserve any returned native owner.
The revision fence also applies to close: a stale copy cannot close the same
connection token or release a copied lifetime claim after a newer continuation
has taken ownership. A failed
publication retains both the before/attempted-after records and native owner
so cleanup can reconcile only those exact candidates, never adopt an arbitrary
newer record.

The new route uses the canonical owned zero-timeout lock, retaining release
errors and unknown outcomes. A blocking legacy Unix lock twin was reported for
separate repair; this route does not fall back to that legacy API. File IO and existing CLI observation may still block;
this design does not claim to complete asynchronous CLI observation support.

## Required acceptance

Authored prevention cases must cover changed payload under the same operation,
corrupt and unknown records, first-publication conflicts, stale copied revision,
partial create submission, expiry between IO steps, retained cleanup, durable
birth before start, unknown start followed by exact-ID inspect, and restart
without create replay. Positive live acceptance must independently observe the
actual native exec ID and exit/output; parent-container exit and helper cleanup
are insufficient evidence. No build or runtime qualification is inferred from
the presence of these tests or from earlier primitive Unix-owner checks.
