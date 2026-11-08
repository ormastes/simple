# Host execution ownership

Status: source integration in progress; executable qualification NOT_RUN.

The canonical orchestrator command and configured local in-process controller
both call `host_local_command_v1`. The host owns its independent V2 operation
journal and physical capacity ledger. Signed controller assignment, host prepare
and host execute authority remain separate; neither transport success nor a
request codec is an authorization decision.

The host executor depends only on Simple Container API V2. Linux uses Podman;
Windows uses Windows Docker process isolation. The common facade dispatches to
platform leaves and returns the updated owner with every operation result.
Actual engine arguments and native identity observation belong to those leaves.
A mismatched backend refuses before journal begin/native dispatch.

The existing physical ledger charges prepared, executing and unknown resources.
Immutable request/plan/proof storage precedes begin. Exact native creation identity
is retained before start; independent inspect precedes the initial observation.
The observation is a start fact, not completion. Repeated executing/unknown work
cannot create a new launch lease. A finite command closes only its exact writer.

Native boot identity and public host aliases are separate. V2 outer scope records
native machine, real native boot or explicit service incarnation, service scope
and provider generation. The legacy ledger/runtime boot slot carries only a
canonical opaque scope fence in the V2 adapter. It is never an OS attestation.

Windows persistent startup mints a native random service epoch and begins
quarantined. The host acquires its existing journal writer, refreshes complete
managed inventory, matches old immutable requests and charges, cancels proven
no-effect preparations, and retains unknown charges. A persisted startup receipt
binds actual journal sequence/revision and inventory; only then may the common
owner accept a typed quarantine acknowledgment. The selected journal profile is
process-crash-v1, not power-loss durability. Actual SDK startup/installed service
root composition is still being connected; codec coverage is not readiness.

Helper admission uses separate signed actions and the same physical ledger.
The signed controller parent budget bounds parent plus every retained sibling;
missing sibling provenance refuses admission. Full helper packets and execution
proofs are retained, but no serialized helper lease conveys authority. The
persistent stream consumer must retain native group owner plus sole reader and
return exact reap evidence before host acknowledgment or resource settlement.

Service broker overhead is a signed immutable partition deducted once from
physical capacity, not once per helper. The native broker policy must verify its
own CPU/memory caps and approved placement. Workload workspace storage requires
an explicit versioned same-ledger quota charge and real native workspace owner;
V1 no-storage reservations cannot be upgraded implicitly.

Outstanding platform gates include admitted self-hosted compilation, real Linux
and Windows lifecycle fixtures, persistent crash/restart recovery, terminal wait
and cleanup evidence, quota-enforced workspace admission, and helper reap
settlement. No source-only result substitutes for those gates.
