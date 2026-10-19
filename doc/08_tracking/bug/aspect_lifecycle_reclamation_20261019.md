# AD-02: drained aspect acquisitions exhaust permanent lifecycle slots

Status: source port prepared, seven regression scenarios UNRUN. Baseline:
`e74e7f6529e5d559c72cc32a578af4d54ce7351b`, including landed AD-01.
Requirement: P4 lifetime closure and P5 bounded resources in
`doc/03_plan/generic_formal_verification_hardening_plan.md`.

## Confirmed source behavior

`aspect_dynload_lifecycle_create_v1` formerly appended one permanent row per
bound acquisition and refused after 1024 total rows. Both ordinary paired
release and successful final unpin consumed external ownership without returning
the retired lifecycle storage. Sequential fully drained acquisitions could thus
exhaust the global registry while using only one simultaneous mapping/reference.
No runtime exhaustion was reproduced in this lane.

## Reviewed design port

This ports the previously independently reviewed AD-02 revision2 source design
from `generic-seven-audit-20261017/aspect-reclamation-fix-v2`. It preserves the
stronger landed AD-01 two-reference/two-execution regression. Each lifecycle
handle, execution lease and snapshot now carries a positive allocation
`incarnation` as well as slot ID. Reuse increments this value without wrapping;
slot exhaustion at signed-i64 maximum remains fail-closed. Facet generation is
separate and never replaces the allocation incarnation check. Four constructors
exist in the common owner; no owned source/test manually constructs these types
elsewhere at this baseline. These are in-process records, not a new wire format;
all consumers must be rebuilt together. No binary-layout compatibility is claimed.

The common reclaim API requires exact allocated incarnation, Retired state,
zero execution/continuation/fence counts and an empty live-lease dictionary. It
clears payload storage and marks the slot vacant while retaining the last
incarnation. Direct common callers must serialize and own the external lifetime;
the helper is not an authentication boundary or implicit lock.

The product gate is the sole mutation authority. Ordinary release retains the
AD-01 drain check, consumes both lower pins once, retains progress flags across
refusal, then retires/reclaims and deactivates. New execution refuses partially
released rows. Capacity refusal precedes acquiring either lower pin or allocating
a lifecycle. Final release reclaims only after physical completion, dynSMF and
aspect commit and native acknowledgment. Retained terminal operations replay
without revisiting a reused lifecycle.

Native release remains outside the logical gate. Dispatch/resume is factored
through the existing production path: resume reacquires the gate, rereads the
canonical final row and honors an already-terminal result before reclaim. It
validates a retained physical-owner receipt for nonterminal continuation;
caller-supplied completion flags grant no release authority. This prevents the
original dispatcher's late continuation from changing another caller's completed
release into a reclamation failure after slot reuse. The deterministic test uses
real dispatch and public recovery, not fabricated progress or thread scheduling.

## Resource and failure contract

At most 1024 lifecycle slots remain allocated; slot search is O(1024) on creation,
not on callback entry/completion. Ordinary handle resolution is O(1); existing
loader row searches retain their existing bounds. Terminal reclaim uses a keys
snapshot bounded by the 4096 live-lease limit, after rejecting nonzero counters.
This differs from the old packet's Dict.len check because the retained actual
probe in `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md`
records erased native receivers returning -1 even for empty dictionaries. No
runtime claim that every current receiver takes that path is made. No new native
allocation or copy cost has been measured; the array/dictionary implementation
and runtime qualification remain open.

Other cumulative limits are unchanged: 16384 bound/query rows and 4096 execution,
final-operation and mapping receipt caps. This does not promise unlimited reloads
or reclaim those independently authoritative rows. Failed native release remains
retryable only through its existing explicit protocol. Exceptional gate-loss or
provider-inconsistency paths stay fail-closed and may quarantine ownership; this
change does not assert full fault-injection leak freedom. Existing registry
serialization and inherited fixture/native-counter prerequisites remain.

Seven new real API scenarios cover repeated reuse, stale handle/lease/duplicate
reclaim, live continuation/fence refusal, incarnation overflow, actual bound
acquire/release beyond the lifecycle cap, final replay after reuse, and native
completion interleaving. All are UNRUN; no compiler, build, test, native replay or
benchmark was launched. Generic body/ABI publication and formal refinement remain
separate open work.
