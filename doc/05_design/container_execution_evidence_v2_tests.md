# Container execution evidence integrity test scope

Eight focused SSpec cases target actual execution_evidence_v2 public helpers.
Owner source SHA-256 at review: `568d43b2accbd7ecd48d1c994f794a70eabfb22a1624d9f7f94a0a653ab2e500`.
No production source was edited. Case titles are the exact frozen step names.

The fixture constructs RuntimeCommand/RuntimeOperation data, full64-character
native identities and separate absence receipt values for both exact backends.
These are PURE integrity fixtures. They do not run native commands, authenticate
a provider, prove actual absence or authorize parent acceptance/capacity release.
They do not construct SimpleContainerOwner or replace any platform adapter.

Query digests are checked against independent canonical SDN of operation/program/
argv, preserving program spaces, argument boundaries, ordering and empty strings.
Observation tests alter every captured field and all runtime identity members.
Terminal construction rejects blank cached query programs, wrong wait/action/
phase/status/exit and tombstone proof_kind. Scope/projection tests cover native ID
length/exact correspondence, UID/attempt/operation/generation, request/provider
pins and service/native continuity separation via opaque all-field scope fences.
Wire tests cover strict unknown/type/duplicate/noncanonical nested source and
UTF-8 bounds for query/observation/evidence input.

Within these documented integrity-only semantics no P0/P1 defect was found.
Digest syntax alone cannot prove that a supplied query ran, targeted the expected
object or observed absence. Actual leaf constructors must use their routed query
and verified full native ID/exit/output; host authentication and parent checks
must compare expected identities before resource retirement. RuntimeOperation's
exit_code is hashed as supplied; tests do not infer raw CLI semantics or status
from that number alone. The actual provider owns the meaning of its observation.

No build, SSpec execution, native query, parser qualification, manual generation,
coverage or signed/full-system acceptance ran. Status: NOT_RUN/awaiting verification.
Prior green checks were not rerun. Authored shorthand ORCH-02/HOST-02 traceability
intent remains subject to the existing requirement reconciliation.
