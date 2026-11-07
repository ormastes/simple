# Signed helper admission in the host physical ledger

Status: source reviewed; six executable scenarios authored, NOT_RUN.

`HostHelperRequestV1` binds the shared helper plan, immutable reservation and
operation, preparation signatures, controller parent-budget proof and exact
parent assignment/host/controller operation chain. Its bounded canonical codec
restores the existing assignment reference; neither decoded data nor retained
bytes are execution authority.

`host_helper_prepare_v1` verifies real helper and controller-budget signatures,
current scope/policy/time, retained parent intent and the parent plus all charged
helper siblings. It archives full immutable packets and admits through the
existing capacity owner. Missing sibling provenance refuses admission. There is
no helper scheduler or second resource ledger. CPU/memory are positive; helper
lifetime cannot exceed the signed parent-budget operation duration.

`host_helper_begin_v1` requires the exact original journal row still admitted,
verifies separate host_helper_execute_v1 signatures and the current budget,
archives execution proof, refreshes authority after filesystem synchronization,
then commits begin before returning a transient HostHelperLeaseV1. The lease
retains the original helper operation and prepared receipt, verified deadline,
actual execution grant/issuer/approver IDs and charged CPU/memory. Preparation
and execution grant IDs stay distinct. No lease codec exists.

`host_helper_request_load_v1(root,operation_id)` verifies the canonical immutable
operation index, content hash, full packet schema and exact operation identity.
`host_helper_execution_proof_load_v1` returns correlated canonical proof bytes.
Both are data loaders; the service must revalidate current authorization before
begin. Executing/unknown replay refuses before object IO and cannot issue a new
lease. A copied lease still needs a downstream exact one-use native consumption
claim; the common stream/broker owns that separate prevention boundary.

The selected journal durability is process-crash-v1. File/directory sync of
archives does not imply power-loss-safe WAL. Resource release is not implemented
by close/expiry after begin; exact group reap plus host acknowledgment is required
by the subsequent settlement owner. Native CPU/memory enforcement belongs to the
versioned process owner, and is not inferred from ledger accounting alone.

Source/prevention inventory: see the authored manual
`doc/06_spec/03_system/app/orchestrator/feature/host_helper_owner_spec.md`.
