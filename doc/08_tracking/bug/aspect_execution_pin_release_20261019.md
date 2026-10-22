# AD-01: ordinary bound release can outlive its execution owner

Status: source repair prepared; regression UNRUN. This is a semantic port of
`generic-seven-audit-20261017/aspect-lease-fix/ad01.patch`, previously reviewed
in isolation. Release baseline `8b944440bd1e5a6522a060abadd301b78cc981e3`
still lacked the guard. It implements the P4 lifetime requirement in
`doc/03_plan/generic_formal_verification_hardening_plan.md`; it does not complete
generic body compilation or dynamic loading.

## Concrete trigger and consequence

Acquire two bound references A and B to the same admitted dynSMF facet. Begin
execution through A. `ModuleLoader.release_bound_facet_v3(A)` previously drained
A's dynSMF query and aspect pin without checking A's lifecycle. B could then
reserve final close. Its final-release check inspects B's lifecycle only, which
has no outstanding execution. Physical release could therefore unmap the
shared code while A's execution lease remained live. This is source-established;
no crashing execution was performed or claimed.

The reference's legacy `release()` already refuses paired V3 references, so
this fix belongs to the public paired release owner, not to a generic raw unpin.
The dynSMF close owner publishes Closing even when it returns query-drain-pending;
ordinary releases must remain retryable after the executing leases finish.

## Repair and invariants

Under the existing lifecycle gate, resolve the selected bound row and take its
canonical lifecycle snapshot before either pin is drained. Refuse a missing
lifecycle or any outstanding execution. Refusal leaves both pins, the active
reference, and release flags intact. Completion remains callable during Closing;
a subsequent explicit release drains exactly once. No new quiescence transition
or automatic retry is introduced. Other provider failures retain the existing
partial-drain flags and retry behavior.

The guard adds one constant-sized snapshot and O(1) counter/index work to the
existing bounded-row lookup; it adds no scan, cache, retained row, native call,
wait, or capacity change. Gate ordering and physical-release ownership remain
unchanged. This is a source complexity argument, not measured allocation,
latency, concurrency or performance evidence. Existing retained lifecycle/handle
capacity and reclamation work (AD-02) remains separate.

## Regression and limits

`test/01_unit/compiler/loader/aspect_final_unpin_v3_authority_spec.spl` now checks
two references and two executions on A. Release refuses before and after B's
Closing attempt, and after only one execution completes. Duplicate completion
cannot substitute for the remaining lease. After final completion A releases
once, rejects new execution/release, and B physically releases once; replay
cannot dispatch another native release.

The existing fixture builds canonical SMF code through SmfWriter, admitted
registry and actual native mapping owners. Mapping/unload observations use their
public counters, not injected addresses or fabricated counts. The test does not
execute a function pointer and is not proof of generic native body support.
Existing suite fixture paths and native counter/runner behavior remain inherited
qualification prerequisites; isolated parallel fixture behavior and allocation
failure injection are not covered by this change. All tests are UNRUN; the
pre-fix false assertion is source-predicted RED only.
