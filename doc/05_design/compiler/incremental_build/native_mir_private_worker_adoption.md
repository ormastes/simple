# Native MIR worker private output and parent observation owners

Status: source integration candidate; executable acceptance UNRUN. No bootstrap
eligibility guard, default-backend selection, action-cache lookup or all-PASS
link gate is relaxed.

Existing selective workers use the existing ledger slot pool. Each invocation,
owner index and replacement generation receives a fresh atomically created
private native-cache and temporary root. The parent installs those environment
values only around spawn and restores them immediately; queue/source/declaration
inputs retain their existing read-only selective admission. The retained producer
header is hashed from the sealed manifest, rather than supplied by a child.
Physical job identities bind the sealed manifest and actual dynamically claimed
module, never an arbitrary pre-spawn job label.

The parent observes the spawned process birth identity before polling/reaping.
Each attempted spawn, timeout, replacement and fail-fast cancellation retains its
owner, root, PID, birth, monotonic lifetime, original exit and confirmed leader-reap
state. Spawn failure retains PID -1 and empty birth; it never manufactures a
process. Existing protocol_complete/recoverable_no_claim and all_stopped remain
the outcome authority. The parent publishes immutable bounded canonical SDN at
`worker-launches.parent.sdn`, including the original physical manifest order.
These launch observations alone do not establish codegen overlap or descendant
quiescence. Existing raw PID cancellation has no retained tool-tree terminal
capability; coordinator admission remains blocked on the existing managed
process-tree owner, as recorded in the lifecycle bug below.

The separate object publication leaf accepts an actual frozen native capsule,
validates it through its existing owner, then publishes a compact bounded SDN
receipt. The parent adoption helper requires independently supplied original
source/configuration/manifest/provider/job/process expectations, verifies bounded
no-follow object and capsule readback, and retains verified bytes in immutable
CAS. CAS storage grants no action-cache-hit or link authority. NonREADY original
rows need no invented child identity and keep the original failed verdict.

The interval leaf admits bounded canonical raw timing only against independently
retained job/producer/child birth/lifetime expectations and the actual capsule
outcome. Its aggregate retains ordered complete frame digests and a parent
result-ledger digest; B computes overlap only from that admitted DTO.

Remaining integration: the bootstrap owner must pass B's complete original
inventory and independently admitted source/provider binding to parent object
adoption, join actual claims/terminal outcomes to retained launch observations,
and publish its validated interval aggregate. This change does not substitute
worker-provided expectations or a success flag for that authority. The current
coordinator records launches; it does not yet call the adoption helper or claim
production partial-result reuse.

Required acceptance remains actual canonical Cranelift job1/job10 equivalence,
at least twelve real physical emissions with measured codegen peak >=10 and
never above admitted 10, mixed-duration refill, unique writable roots, original
HIR failure plus independent compile failures with no link, stale context/child
birth refusal, and timeout/SIGKILL/cancel descendant quiescence. Synthetic codec
and interval-accounting tests cannot qualify those claims. All runtime tests,
including the real worker artifact adoption fixture, remain UNRUN pending a
qualified self-hosted CLI/provider/runtime. No new runner or seed fallback.

The lifecycle source defect and remaining admission blocker are recorded in
`doc/08_tracking/bug/native_mir_raw_process_lifecycle_identity_gap_2026-10-25.md`.
A successful wait now prevents subsequent PID probing/termination, but this
source repair does not qualify cancellation or managed descendant cleanup.

## Managed owner integration candidate

The follow-up now routes selected workers through the existing Linux durable
broker with version-three generic argv requests, explicit cached launcher,
retained startup uncertainty, broker-issued actual PID/birth identity, and
lease-bound terminal tree collection. Private environment values are copied
into each explicit request rather than installed globally around spawn.
See `doc/04_architecture/compiler/native_mir_managed_process_owner_v3.md` for
owner lifetimes, platform/error contracts and the UNRUN acceptance gates.
The coordinator now records managed request/tree receipt identities; the final
original-inventory/provider-bound object adoption caller remains separate.
