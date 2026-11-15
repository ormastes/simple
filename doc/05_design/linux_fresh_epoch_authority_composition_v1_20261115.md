# Fresh Linux epoch authority and creator composition

Status: SOURCE_IMPLEMENTATION / AUTHORED_NOT_RUN. Base: release commit
`b8b14272484fd826852425afcb1bf6df28102443`; isolated worktree
`/tmp/simple-linux-fresh-upper-admission-20261115-b8b142`. No privileged setup,
compiler, test, runtime, bootstrap or native campaign was run. The selected
parent design is `linux_fresh_provider_epoch_admission_v1_20261115.md`
SHA256 `3f50599c94a0b4b9bd6d8cd18aa8cd0f5445a5bc108ddc0164dde4a23cb4c52d`.

## Selected behavior and requirements

| Requirement | Source behavior | Evidence |
|---|---|---|
| REQ-LINUX-FRESH-EPOCH-001 | Genuine installed preparation and an actual authenticated standalone principal bind the original machine writer to exact physical, policy, partition and store identities. | Actual fixed-profile fixture spec; NOT_RUN. |
| REQ-LINUX-FRESH-EPOCH-002 | Same-WAL scope and creator intent precede a one-shot actual profiled creator; copied permits cannot spawn twice. | Canonical lifecycle tests and actual copied-owner scenario; NOT_RUN. |
| REQ-LINUX-FRESH-EPOCH-003 | Every native output survives a post-effect failure; cleanup consumes only confirmed actual owners and never refunds charge. | Actual fixture cleanup and source ownership review; native faults NOT_COVERED. |
| REQ-LINUX-FRESH-EPOCH-004 | Generic missing-CURRENT, unknown history and managed two-row fresh-genesis refusals remain unchanged. | Separate fresh entry/record scheme; source review, native negatives pending. |
| REQ-LINUX-FRESH-EPOCH-005 | Exact known first history may resume custody without a second genesis; ambiguous publication and creator replay cannot mint another launch. | Strict history codec and canonical phase tests; crash execution NOT_COVERED. |

This first positive path starts one actual owned Podman cgroupfs provider
process. Its `Started` result confirms the owned profiled process, not an
endpoint peer, workload PID/cgroup relationship, transport client or workload
reservation. Those distinct facts remain required before a workload grant.
The generic `process_admit_v1` refusal is retained. There is no automatic fresh
fallback for a remote caller, an existing store or an unknown ledger.

## Actual call chain and ownership

The previous generic authority path opens installed policy, authenticates its
actual local principal, probes the provider, opens storage and checks CURRENT.
The provider probe can initialize Podman storage. Generic Linux commit also
rejects an empty expected parent. Removing either check without proof would
turn missing accounting into capacity.

The new explicit chain is:

```text
local_container_service_start_fresh_epoch_v1(template DATA)
  -> machine_container_authority_open_fresh_epoch_v1()
  -> genuine zero-argument installed epoch preparation
  -> original policy reader -> SAME original machine storage writer
  -> actual local principal + exact native/policy correspondence
  -> proof-bearing fresh head/closed-schema commit
  -> exact actual first-history replay
  -> same-registry preparation-to-successor custody transfer
  -> private MachineFreshEpochAdmissionOwnerV1
  -> installed/native-derived bound launch DATA + restrictive validation
  -> SAME-WAL creator intent and uncertain overhead update
  -> canonical one-shot consume BEFORE process_spawn_piped_owned_v2
  -> retained actual process + writer + successor, or retained cleanup
```

The new fresh opening skips provider observers only when holding the genuine
preparation capability. Generic opening still refuses missing CURRENT and
performs its existing observations. There is no public `fresh=true` switch,
policy/path argument or observation-to-grant constructor.

The dependency graph stays acyclic. Platform Linux storage imports the pure
record codec; the opaque epoch owner imports platform storage, not the neutral
facade. The facade imports the actual epoch owner and record codec. Authority
imports those and small projection/history/lifecycle helpers. Provider and
service consumers import authority, while authority never imports them.
Existing canonical paired cleanup remains in place without extraction.

The platform fresh head/commit mechanisms accept a closed record and return
revision data only. The facade requires actual preparation and rechecks every
observation field, installed machine/provider policy, principal UID, physical
bounds and exact native storage identity before calling them. A decoded record
or revision cannot construct the private upper admission.

The native store digest includes retained graph/run identities and the exact
machine state/WAL/object-root identities. It is not a path hash. The original
writer stays held throughout first charge, handoff and actual creator use;
no writer getter, second journal or unlock interval is introduced.

Ownership follows the parent-authoritative process boundary:

| Boundary | Classification and canonical owner |
|---|---|
| Machine WAL and snapshot revisions | Actual retained handle; original storage owner performs CAS and validates exact parent/order. No child receives mutable ledger state. |
| Preparation to successor | Owned same-registry handoff; source aliases are invalidated before the successor is returned and all partial outputs remain retained. |
| Bound launch to profiled native creator | Validated encoded/frozen copy using existing V2/V3 ABI/wire. It contains no parent raw pointer or machine-writer handle. |
| Native process return | Child-created actual owned handle plus optional exact reference, retained before fallible attachment/postchecks. |
| Copied admission or cleanup value | Alias to a private canonical origin/thread-scoped slot, never an independent startup or close right. |
| Exceptional unattached process | Pre-reserved opaque cleanup token; exact native identity/reference and confirmed consumption are recorded canonically, not inferred from raw stale. |

Existing persistent/ABI layouts remain pinned; this change introduces no
process codec, device lease, scheduler or shared mutable child object. Unknown
dynamic effects remain overlapping/uncertain and are never another free pool.

## Canonical accounting

The existing Host subtract-before-sum validator checks three Uncertain
reservations: conservative outside obligations, reserved Host/provider overhead
and usable partition capacity. `observed = reserved + usable`; outside plus
observed cannot exceed either actual physical capacity or installed policy.
The codec compares before adding and rejects negative/overflowing declarations.
CPU quota is a maximum, not an exclusive-core reservation. Device grants are
empty, and no GPU, workspace quota or mount authority is inferred.

The first revision has four canonical rows in the existing scope/reservation
tables: one immutable fresh-epoch binding and the three charges. This is a
separate schema from the existing managed two-row history. Unknown, changed or
mixed history refuses rather than being reset.

Creator admission appends exactly two rows under the same writer: full bound
normalized template intent and an Update of the already charged overhead row
to an uncertain creator debit. It does not create a second capacity pool.
Native readback verifies the first revision and this exact child revision
before launch. Replayed intent data is not a reusable spawn grant.

Historical process digest, manager unique name and registry generation are
stored as observations, not a reboot epoch. Stable installation comparison
excludes those three fields. Actual new custody is still mandatory; matching
stable bytes alone cannot admit recovery. Current successor generation is
captured privately and checked before each creator use.

## Publication and crash boundaries

| Boundary | Required retained state and behavior |
|---|---|
| Before first mutation | Actual preparation, reader/storage, principal and original writer remain owned. No provider observer/creator has run. |
| Policy binding before CURRENT | Lower `binding_created_here` eligibility is tied to this actual held writer. A crash or ambiguous binding without CURRENT requires explicit operator repair, not automatic retry. |
| Initial commit attempt | Eligibility is consumed before mutation. Any CAS/readback uncertainty retains ownership and potential charge; no second genesis/reset is attempted. |
| Verified initial four-row revision | Exact replay may continue the custody handoff without another accounting commit. Missing/changed history refuses. |
| Preparation transfer | The lower canonical owner invalidates preparation aliases before returning successor custody. Both actual outputs are captured before errors are interpreted. |
| Creator intent CAS | Canonical phase changes before the write. An ambiguous outcome blocks reuse and retains the unknown overhead charge. |
| Intent verified, before native call | Canonical permit consumption precedes native spawn. A copied admission cannot issue another startup call. |
| Native outcome or postcheck failure | Actual Ready/CleanupRequired outputs are retained before attachment, identity or response checks. No data-only rejection erases them. |
| Cleanup | Retire the exact actual process first, then machine writer, then native successor custody. Only confirmed consumption clears a component; raw stale/unknown remains retained. No charge is refunded. |

The first actual cleanup diagnostic is recorded immediately in the canonical
lifecycle, before a pending turn returns. Thus close(A) may retain an error and
close(B), an alias, can later finish without losing that first diagnostic.
Ordinary value-copy error fields are not the sole record of cleanup progress.

Exceptional process cleanup is reserved before the native call and has distinct
unresolved, actual no-owner rejection, transferred and positively consumed
states. The exact returned native identity/reference is captured before policy
postvalidation. Copies retry the actual native close only until this same
scope has positively consumed it; they never interpret `stale_process_reference`
as completion. An unresolved fallback blocks closing the machine writer.
The candidate progress reducer is modeled in tests, but production commits a
consumed candidate only after the real owned native close succeeds.

General populated-store restart recovery remains NOT_COVERED. The new upper
opening accepts only exact initial four-row history before any creator child
revision; it refuses a prior creator/unknown descendant instead of relaunching
from replay data. Existing-store migration, Stop/Mask and label adoption remain
outside this profile.

## Launch producer and trust boundary

The root-installed epoch profile has 34 mandatory fields, including actual
protected `brokerExecutable` and `brokerExecutableSha256`. Lower successor
binding derives effect-bearing launch data from installed/native facts;
strict validation checks program/broker identity, safe run-root child, empty
child inputs/environment, directory, image mode, cgroup identities/generation
and CPU/memory caps. The caller's template is never broker authority.

The broker inherits the root-provisioned trusted Host service environment.
That environment is trusted input under selected profile B and cannot be
altered by an untrusted client. An exact empty child environment is not a
claim that the inherited broker environment was sanitized. No request-supplied
environment becomes service provisioning. The environment is assumed stable
while this trusted Host owner runs.

Only an actual private durable admission holding actual successor custody can
reach the creator. A fresh preparation, current snapshot, profile digest,
principal label or correctly shaped template alone cannot start a process.
The creator stamps a bounded local pre-exec deadline after validating normalized
template data; existing native profiled creation checks it before exec.

## Verification limits

Five record scenarios and four production lifecycle scenarios are authored.
One actual administrator-provisioned fixture scenario exercises first charge,
profiled startup, copied second-start refusal, actual cleanup and persisted
unknown creator debit. No fake opaque owner, synthetic positive WAL preseed or
conditional passing oracle is used. All are NOT_RUN; no coverage percentage,
native acceptance, runtime performance or release readiness is claimed.

Source retention is bounded by the existing native process owner plus 256
nonreused canonical lifecycle slots. Slot exhaustion refuses with original
ownership retained. Startup/request latency, resident memory and actual native
fault behavior remain unmeasured. Provider endpoint readiness, daemon peer
authentication, workload correlation and populated epoch recovery remain
separate acceptance work.
