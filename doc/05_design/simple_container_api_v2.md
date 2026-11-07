# Simple Container API V2

## Portable contract and actual platform delegation

execution_v2.spl contains only pure common values/canonical codecs. api_v2.spl
contains the tagged owner routing actual LinuxSimpleContainerAdapterV2 and
WindowsSimpleContainerAdapterV2 classes. No trait-probe-only implementation,
duplicate scheduler/journal, raw runtime call or automatic fake provider exists.
Exact backends are linux-podman and windows-docker-process; no backend guessing.

SimpleContainerOwnerV2 has Linux(scope,adapter) and Windows(scope,adapter) tags.
ContainerOperationTurnV2 always returns owner plus RuntimeOperationV1, including
refusals. Platform me apply/read/recover methods update the tagged owner returned
to the caller. Unknown actions and common request/scope/projection mismatches
produce rejected operations with the original owner and unknown runtime state;
rejection is not proof that native work is absent or capacity can be released.

API functions: simple_container_observe_v2/open_v2/project_v2/apply_v2/read_v2/
recover_v2/intent_v2, plus effect-free scope/backend accessors. Observe/open use real static adapter methods. Open validates
the adapter's CACHED actual observation; it does not issue a second engine probe.
All lifecycle entrypoints validate common scope and actual leaf projection before
calling a mutating platform method. Backend semantic request digest/identity
validation remains in the actual leaf, not duplicated in common.

## Identity, aliases and honest continuity

ContainerHostScopeV2 binds physical_host_id (authorized ALIAS), native_machine_id
(actual identity), service_scope_id, provider_generation, boot_id, continuity_mode
and continuity_id. Native machine/continuity IDs accept at most256 ASCII
alphanumeric/underscore/hyphen/colon bytes (including Windows provenance prefixes),
with no whitespace or path separators; physical/service aliases retain strict
builder identity validation. Plan additionally binds backend/workload/attempt/operation and
semantic request digest. The authorized alias is NEVER compared to observed
native_machine_id. Native machine and native boot are checked against their own
explicit fields, along with the administrator provider-identity pin.

native-boot-incarnation-v1 requires a nonempty native boot and continuity_id equal
to boot_id. service-incarnation-v1 requires boot_id EMPTY and a separate nonempty
persistent owner incarnation ID. Pure codecs preserve either form; a canonical
service scope does not prove persistence or authorize continuity on its own.
Current finite open admits NATIVE mode only. Persistent service-incarnation
factory/quarantine is not implemented here; it must be a later explicit owner.

ContainerHostObservationV2 carries actual machine, native boot, provider identity,
execution OS/architecture and continuity_assurance/boot_observation. A native
incarnation has nonempty native_boot_id. machine-boot-counter-v1 requires EMPTY
native_boot_id and a nonempty actual weak boot observation. Observe validates
that honest shape but grants no continuity. Current open refuses weak assurance,
including the diagnosed weak Windows path, rather than fabricating OS boot IDs.

container_scope_fence_id_v2 hashes canonical bytes of ALL seven scope fields.
New V2 adapters use this opaque hash in legacy RuntimeIntent/RuntimeIdentity
node_boot_id slots solely for internal fencing. It is NOT OS boot evidence.
Existing V1 direct leaf calls retain their existing semantics and are unchanged.

## Wire and effects

Scope/plan/request codecs are version2 canonical SDN. Scope and plan source limits
are16KiB; opaque body limit1MiB and outer request limit2MiB count UTF-8 BYTES using
common.string_core.str_len. Unknown/duplicate/wrong-type/noncanonical records fail.
Nested escaping can exceed aggregate budget despite a valid individual body;
reject the packet without truncation. Provider semantic digests are not assumed
to equal raw request-byte SHA-256. Common imports no provider/platform leaf.

Exact apply actions: prepare/create/start/inspect/logs/wait/stop/destroy. Explicit
read accepts ONLY inspect/logs/wait and has NO deadline parameter. Apply delegates
those reads to the read port. Leaves enforce ContainerEffectDeadlineV1 against
actual clock immediately before create/start/exec/attach effects only. A launch
deadline is not a workload lifetime and cannot authorize grant-driven killing.
Read/recovery need no fabricated launch eligibility. Stop/destroy require
separate caller-verified live cleanup authority or retained authorized lifecycle
ownership; expired launch eligibility is never cleanup permission.
Recover validates immutable request and opaque legacy intent fence before leaf
recovery; it does not invent a fresh launch deadline or grant retirement.

## Tests, dependencies and status

Common executable/probe: container_execution_v2_spec.spl and fixture
orchestrator_acceptance/container_execution_v2.spl. Eight scenarios cover both
exact backends, canonical hashes, identities, strict wire/bytes, alias separation,
service/native continuity and all-field scope fences.

API executable: simple_container_api_v2_spec.spl; fixture
orchestrator_acceptance/simple_container_api_v2.spl. Its route helper consumes
ACTUAL API-opened owners and real backend request bytes. Configured Linux/Windows
cases require administrator fixture paths/pins; missing or weak native runtime
fails rather than skips/passes. Guard or projection tests are not native lifecycle
qualification. Each platform owner must exercise real lifecycle/nonce/inspection
through the same API and an independent provider oracle.

The test-only container/simple_container_api_fixture_v2.spl wrapper accepts an
actual scripted Linux adapter ONLY after is_scripted_fixture_v2() succeeds. It is
never imported by production API and never counts as native Podman/Docker proof.

Pending parallel source dependencies: effect_deadline_v1 and both actual adapter
modules. No stub is supplied for them. Current live Windows continuity bridge is
still required. No build or native/SSpec/manual-generation/coverage run is made;
status is NOT_RUN/awaiting verification, not a full runtime support claim.
