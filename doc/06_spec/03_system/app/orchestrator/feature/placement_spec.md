# Placement proposal acceptance scenarios

**AUTHORED_NOT_RUN.** Authored modern SSpec manual, not generated execution
evidence. Actual compiled SSpec execution and `spipe-docgen` validation with zero
stubs remain pending the admitted full CLI/test runner.

Source: `test/03_system/app/orchestrator/feature/placement_spec.spl`.
Requirements: ORCH-01, ORCH-02, HOST-02. Supports AT-ORCH-01 and AT-ORCH-02 at the
**pure production decision/transition** level. Does not qualify live admission,
physical GPU exclusivity, provider enforcement, or a network partition.

## Fixture and oracle

Each case constructs typed inventory and profile values and calls
`plan_host_placement_v1`. Those values are data, not usable native capabilities or
authenticated authority. Host preparation uses the existing pure ledger
transition; it does not publish a durable grant. No file or runtime cleanup is
needed because these scenarios allocate no native resource.

Assertions retain literal expected host/device identities, quantities and error
codes rather than deriving the expected value from the selected offer alone.
Fourteen existing scenarios are retained; three new cases cover exact CPU/memory
floors, one-byte memory shortage, and a single uncertain exclusive GPU after
reducing CPU/memory demand. All 17 are registered source cases, not executed counts.

## Scenario flow

### Should place Windows requests only on the explicit Windows Docker runtime class
1. Keep Windows Docker eligibility separate from Linux Podman hosts.

### Should preserve GPU hosts for CPU work and publishes effective caps
1. Prefer a feasible CPU host and inspect reserved-equivalent caps.

### Should queue below minimum and exposes the rejection reason
1. Refuse a host below the declared CPU floor.

### Should allocate between minimum and recommendation without increasing caps
1. Expose constrained admission instead of pretending to meet recommendation.

### Should reject duplicate physical capacity and unsupported GPU sharing
1. Reject two inventory rows for one machine and an unqualified sharing mode.

### Should never downgrade a required GPU claim to CPU
1. Require an explicit GPU claim and a feasible device.

### Should require current authorization health and enforcement
1. Refuse unauthorized, draining, unhealthy and unenforced host snapshots.

### Should reject stale continuity and mismatched runtime eligibility
1. Refuse uncertain inventory and mismatched execution targets.

### Should use a stable host identity tie break independent of inventory order
1. Permute equivalent hosts and preserve the selected identity.

### Should bind the selected offer and attempt identity into canonical host intent
1. Carry exact host fence, allocation and immutable plan identity to admission.

### Should refuse to construct a reservation for a queued or invalid selection
1. Reject missing selection before indexing any host or creating an intent.

### Should reject unresolved devices or allocation and cap disagreement
1. Fail closed on an inconsistent programmatically constructed offer.

### Should propose exactly one available GPU across inventory permutations and active states
1. Keep a busy first GPU charged and choose the same free GPU for each ordering.

### Should queue when every GPU is busy and reuses only an explicitly released device
1. Keep prepared executing and uncertain claims exclusive until their state is Released.

### Should admit exactly the CPU and memory floors with matching caps
1. Offer exactly the declared minima and expose constrained allocation.

### Should queue one byte below the memory floor despite spare CPU
1. Offer enough CPU but one byte less than the declared memory minimum.

### Should keep the only uncertain GPU unavailable after reducing CPU and memory requests
1. Keep the single exclusive GPU charged while CPU and memory are abundant.
2. Reduce only CPU and memory while preserving the required exclusive device claim.

## Boundary outcomes

- Exactly 1000 millicores and 2000 memory bytes are admitted with equal caps and
  `below_recommendation = true`; neither minimum is silently reduced.
- At 1999 memory bytes with 8000 millicores available, placement has no offer and
  rejects with `insufficient-memory-minimum`.
- An uncertain claim on the only GPU keeps placement queued before and after
  reducing the new request to 500 millicores / 1000 bytes. The existing ledger
  still reports 7000 millicores / 23000 bytes free and zero free devices.
- Prepared, executing and uncertain device claims remain charged in existing
  permutation cases. Only an explicitly Released data row frees a device; these
  tests do not prove the native termination evidence required to authorize that
  transition in the actual Host.

The Windows/docker-process eligibility case checks only typed inventory filtering;
it does not qualify a Windows engine. AT-ORCH-03's real partition behavior requires
a separate actual Controller/Host fixture. Do not count these synthetic snapshots
as multi-user concurrency or physical-device tests.

<details>
<summary>Executable SSpec source (authored, unexecuted)</summary>

```simple
# codex-system-test
# @req ORCH-01 ORCH-02 HOST-02
# @acceptance AT-ORCH-01 AT-ORCH-02
# AUTHORED_NOT_RUN: pure production placement and ledger transitions.
# Synthetic inventory is not live capacity, authorization, or native device proof.
use std.spec.{describe, it, expect, step}
use std.common.contracts.orchestration.placement_v1.*
use std.common.contracts.orchestration.host_capacity_v1.*
use std.common.contracts.orchestration.profile_v1.*
use std.common.contracts.orchestration.resource_v1.ObjectMetaV1

fn placement_request() -> PlacementRequestV1:
    val profile = ResourceProfileV1(meta: ObjectMetaV1(name: "agent", ns: "caret", labels: {}),
        cpu: ResourceAmountRangeV1(minimum: 1000, recommended: 2000, preferred: 4000, limit: 4000),
        memory: ResourceAmountRangeV1(minimum: 2000, recommended: 4000, preferred: 8000, limit: 8000),
        gpu_required: false, preserve_scarce_gpu_hosts: true)
    PlacementRequestV1(pool_id: "development", execution_os: "linux", architecture: "aarch64",
        runtime_class: "podman-rootless", profile: profile, gpu_mode: "none", allow_preferred: false)

fn placement_host(id: text, devices: [text], cpu: i64, memory: i64) -> PlacementHostV1:
    val capacity = HostCapacityV1(physical_host_id: id, authority_id: "machine-owner", boot_id: "boot",
        provider_generation: 1, cpu_millis: cpu, memory_bytes: memory, exclusive_devices: devices)
    PlacementHostV1(pool_id: "development", service_scope_id: "user", execution_os: "linux",
        architecture: "aarch64", runtime_class: "podman-rootless", authorized: true, healthy: true,
        draining: false, limits_enforced: true, gpu_devices: devices,
        ledger: HostCapacityLedgerV1(capacity: capacity, revision: 1, continuity_proven: true, reservations: []))

fn placement_gpu_reservation(devices: [text], state: HostReservationStateV1) -> HostReservationV1:
    HostReservationV1(id: "existing", operation_id: "existing-op", payload_digest: "9".repeat(64),
        service_scope_id: "user", assignment_generation: 1, nonce: "existing-nonce",
        cpu_millis: 1000, memory_bytes: 1000, exclusive_devices: devices,
        prepare_deadline_ms: 100, state: state)

describe "native host placement proposals":
    it "should place Windows requests only on the explicit Windows Docker runtime class":
        step("Keep Windows Docker eligibility separate from Linux Podman hosts")
        var request = placement_request()
        request.execution_os = "windows"
        request.runtime_class = "docker-process"
        val linux = placement_host("linux", [], 4000, 8000)
        var windows = placement_host("windows", [], 4000, 8000)
        windows.execution_os = "windows"
        windows.runtime_class = "docker-process"
        val plan = plan_host_placement_v1(request, [linux, windows]).unwrap()
        expect(plan.offers[plan.selected_index].physical_host_id).to_equal("windows")
        expect(plan.rejected.len()).to_equal(1)
        val refused = plan_host_placement_v1(request, [linux]).unwrap()
        expect(refused.selected_index).to_equal(-1)
        expect(refused.offers.len()).to_equal(0)

    it "should preserve GPU hosts for CPU work and publishes effective caps":
        step("Prefer a feasible CPU host and inspect reserved-equivalent caps")
        val plan = plan_host_placement_v1(placement_request(), [placement_host("gpu", ["gpu-0"], 8000, 24000), placement_host("cpu", [], 4000, 8000)]).unwrap()
        val selected = plan.offers[plan.selected_index]
        expect(selected.physical_host_id).to_equal("cpu")
        expect(selected.allocation.cpu_millis).to_equal(2000)
        expect(selected.allocation.cpu_cap_millis).to_equal(2000)
        expect(selected.allocation.memory_cap_bytes).to_equal(4000)

    it "should queue below minimum and exposes the rejection reason":
        step("Refuse a host below the declared CPU floor")
        val plan = plan_host_placement_v1(placement_request(), [placement_host("small", [], 999, 8000)]).unwrap()
        expect(plan.selected_index).to_equal(-1)
        expect(plan.rejected[0].reason).to_equal("insufficient-cpu-minimum")

    it "should allocate between minimum and recommendation without increasing caps":
        step("Expose constrained admission instead of pretending to meet recommendation")
        val plan = plan_host_placement_v1(placement_request(), [placement_host("small", [], 1500, 3000)]).unwrap()
        expect(plan.offers[0].allocation.below_recommendation).to_equal(true)
        expect(plan.offers[0].allocation.cpu_cap_millis).to_equal(1500)
        expect(plan.offers[0].allocation.memory_cap_bytes).to_equal(3000)

    it "should reject duplicate physical capacity and unsupported GPU sharing":
        step("Reject two inventory rows for one machine and an unqualified sharing mode")
        val host = placement_host("same", [], 4000, 8000)
        expect(plan_host_placement_v1(placement_request(), [host, host]).unwrap_err()).to_equal("duplicate-physical-host")
        var request = placement_request()
        request.gpu_mode = "shared"
        expect(plan_host_placement_v1(request, [host]).unwrap_err()).to_equal("unsupported-gpu-mode")

    it "should never downgrade a required GPU claim to CPU":
        step("Require an explicit GPU claim and a feasible device")
        var request = placement_request()
        request.profile.gpu_required = true
        val cpu = placement_host("cpu", [], 4000, 8000)
        expect(plan_host_placement_v1(request, [cpu]).unwrap_err()).to_equal("required-gpu-claim-missing")
        request.gpu_mode = "whole-exclusive"
        val plan = plan_host_placement_v1(request, [cpu]).unwrap()
        expect(plan.selected_index).to_equal(-1)
        expect(plan.rejected[0].reason).to_equal("exclusive-gpu-unavailable")

    it "should require current authorization health and enforcement":
        step("Refuse unauthorized, draining, unhealthy and unenforced host snapshots")
        val base = placement_host("host", [], 4000, 8000)
        var host = base
        host.authorized = false
        expect(plan_host_placement_v1(placement_request(), [host]).unwrap().rejected[0].reason).to_equal("host-not-authorized")
        host = base
        host.draining = true
        expect(plan_host_placement_v1(placement_request(), [host]).unwrap().rejected[0].reason).to_equal("host-draining")
        host = base
        host.healthy = false
        expect(plan_host_placement_v1(placement_request(), [host]).unwrap().rejected[0].reason).to_equal("host-unhealthy")
        host = base
        host.limits_enforced = false
        expect(plan_host_placement_v1(placement_request(), [host]).unwrap().rejected[0].reason).to_equal("resource-enforcement-unavailable")

    it "should reject stale continuity and mismatched runtime eligibility":
        step("Refuse uncertain inventory and mismatched execution targets")
        val base = placement_host("host", [], 4000, 8000)
        var host = base
        host.ledger.continuity_proven = false
        expect(plan_host_placement_v1(placement_request(), [host]).unwrap().rejected[0].reason).to_equal("host-reconciliation-required")
        host = base
        host.runtime_class = "docker-process"
        expect(plan_host_placement_v1(placement_request(), [host]).unwrap().rejected[0].reason).to_equal("runtime-class-mismatch")
        host = base
        host.architecture = "x86_64"
        expect(plan_host_placement_v1(placement_request(), [host]).unwrap().rejected[0].reason).to_equal("architecture-mismatch")

    it "should use a stable host identity tie break independent of inventory order":
        step("Permute equivalent hosts and preserve the selected identity")
        val a = placement_host("a", [], 4000, 8000)
        val b = placement_host("b", [], 4000, 8000)
        val first = plan_host_placement_v1(placement_request(), [b, a]).unwrap()
        val second = plan_host_placement_v1(placement_request(), [a, b]).unwrap()
        expect(first.offers[first.selected_index].physical_host_id).to_equal("a")
        expect(second.offers[second.selected_index].physical_host_id).to_equal("a")

    it "should bind the selected offer and attempt identity into canonical host intent":
        step("Carry exact host fence, allocation and immutable plan identity to admission")
        val plan = plan_host_placement_v1(placement_request(), [placement_host("host", [], 4000, 8000)]).unwrap()
        val identity = PlacementAttemptIdentityV1(reservation_id: "one", operation_id: "op-one",
            assignment_generation: 2, nonce: "nonce-one", plan_digest: "1".repeat(64), prepare_deadline_ms: 100)
        val intent = placement_reservation_intent_v1(plan, identity).unwrap()
        expect(intent.physical_host_id).to_equal("host")
        expect(intent.fence.revision).to_equal(plan.offers[0].fence.revision)
        expect(intent.reservation.cpu_millis).to_equal(plan.offers[0].allocation.cpu_millis)
        expect(intent.reservation.memory_bytes).to_equal(plan.offers[0].allocation.memory_bytes)
        expect(intent.reservation.assignment_generation).to_equal(2)
        expect(intent.plan_digest).to_equal(identity.plan_digest)
        var changed = identity
        changed.plan_digest = "2".repeat(64)
        expect(placement_reservation_intent_v1(plan, changed).unwrap().reservation.payload_digest == intent.reservation.payload_digest).to_equal(false)

    it "should refuse to construct a reservation for a queued or invalid selection":
        step("Reject missing selection before indexing any host or creating an intent")
        val identity = PlacementAttemptIdentityV1(reservation_id: "one", operation_id: "op-one",
            assignment_generation: 1, nonce: "nonce-one", plan_digest: "1".repeat(64), prepare_deadline_ms: 100)
        val empty = plan_host_placement_v1(placement_request(), []).unwrap()
        expect(placement_reservation_intent_v1(empty, identity).unwrap_err()).to_equal("placement-queued")
        var invalid = empty
        invalid.selected_index = 1
        expect(placement_reservation_intent_v1(invalid, identity).unwrap_err()).to_equal("invalid-selected-offer")

    it "should reject unresolved devices or allocation and cap disagreement":
        step("Fail closed on an inconsistent programmatically constructed offer")
        val plan = plan_host_placement_v1(placement_request(), [placement_host("host", [], 4000, 8000)]).unwrap()
        val identity = PlacementAttemptIdentityV1(reservation_id: "one", operation_id: "op-one",
            assignment_generation: 1, nonce: "nonce-one", plan_digest: "1".repeat(64), prepare_deadline_ms: 100)
        var offer = plan.offers[0]
        offer.allocation.requires_gpu_resolution = true
        val unresolved = PlacementPlanV1(offers: [offer], rejected: [], selected_index: 0)
        expect(placement_reservation_intent_v1(unresolved, identity).unwrap_err()).to_equal("unresolved-device-claim")
        offer = plan.offers[0]
        offer.allocation.cpu_cap_millis = 4000
        val uncapped = PlacementPlanV1(offers: [offer], rejected: [], selected_index: 0)
        expect(placement_reservation_intent_v1(uncapped, identity).unwrap_err()).to_equal("allocation-cap-mismatch")

    it "should propose exactly one available GPU across inventory permutations and active states":
        step("Keep a busy first GPU charged and choose the same free GPU for each ordering")
        var request = placement_request()
        request.profile.gpu_required = true
        request.gpu_mode = "whole-exclusive"
        val identity = PlacementAttemptIdentityV1(reservation_id: "new", operation_id: "new-op",
            assignment_generation: 2, nonce: "new-nonce", plan_digest: "1".repeat(64), prepare_deadline_ms: 100)
        for state in [HostReservationStateV1.Prepared, HostReservationStateV1.Executing, HostReservationStateV1.Uncertain]:
            for devices in [["gpu-2", "gpu-0", "gpu-1"], ["gpu-1", "gpu-2", "gpu-0"], ["gpu-0", "gpu-1", "gpu-2"]]:
                var host = placement_host("gpu-host", devices, 8000, 24000)
                host.ledger.reservations = [placement_gpu_reservation(["gpu-0"], state)]
                val plan = plan_host_placement_v1(request, [host]).unwrap()
                expect(plan.selected_index).to_equal(0)
                expect(plan.offers.len()).to_equal(1)
                expect(plan.offers[0].exclusive_devices.len()).to_equal(1)
                expect(plan.offers[0].exclusive_devices[0]).to_equal("gpu-1")
                expect(plan.offers[0].allocation.requires_gpu_resolution).to_equal(false)
                val intent = placement_reservation_intent_v1(plan, identity).unwrap()
                expect(intent.reservation.exclusive_devices.len()).to_equal(1)
                expect(intent.reservation.exclusive_devices[0]).to_equal("gpu-1")
                expect(intent.reservation.cpu_millis).to_equal(2000)
                expect(intent.reservation.memory_bytes).to_equal(4000)
                val prepared = host_prepare_reservation_v1(host.ledger, intent.fence, intent.reservation, 1).unwrap()
                expect(prepared.reservations.len()).to_equal(2)
                expect(prepared.reservations[1].exclusive_devices.len()).to_equal(1)
                expect(prepared.reservations[1].exclusive_devices[0]).to_equal("gpu-1")
                val remaining = host_available_capacity_v1(prepared).unwrap()
                expect(remaining.exclusive_devices.len()).to_equal(1)
                expect(remaining.exclusive_devices[0]).to_equal("gpu-2")

    it "should queue when every GPU is busy and reuses only an explicitly released device":
        step("Keep prepared executing and uncertain claims exclusive until their state is Released")
        var request = placement_request()
        request.profile.gpu_required = true
        request.gpu_mode = "whole-exclusive"
        for state in [HostReservationStateV1.Prepared, HostReservationStateV1.Executing, HostReservationStateV1.Uncertain]:
            var host = placement_host("gpu-host", ["gpu-1", "gpu-0"], 8000, 24000)
            host.ledger.reservations = [placement_gpu_reservation(["gpu-0", "gpu-1"], state)]
            val blocked = plan_host_placement_v1(request, [host]).unwrap()
            expect(blocked.selected_index).to_equal(-1)
            expect(blocked.offers.len()).to_equal(0)
            expect(blocked.rejected[0].reason).to_equal("exclusive-gpu-unavailable")
        var released = placement_host("gpu-host", ["gpu-1", "gpu-0"], 8000, 24000)
        released.ledger.reservations = [placement_gpu_reservation(["gpu-0", "gpu-1"], HostReservationStateV1.Released)]
        val available = plan_host_placement_v1(request, [released]).unwrap()
        expect(available.selected_index).to_equal(0)
        expect(available.offers[0].exclusive_devices.len()).to_equal(1)
        expect(available.offers[0].exclusive_devices[0]).to_equal("gpu-0")

    it "should admit exactly the CPU and memory floors with matching caps":
        step("Offer exactly the declared minima and expose constrained allocation")
        val plan = plan_host_placement_v1(placement_request(), [placement_host("floor", [], 1000, 2000)]).unwrap()
        expect(plan.selected_index).to_equal(0)
        expect(plan.offers.len()).to_equal(1)
        expect(plan.rejected.len()).to_equal(0)
        val allocation = plan.offers[0].allocation
        expect(allocation.cpu_millis).to_equal(1000)
        expect(allocation.cpu_cap_millis).to_equal(1000)
        expect(allocation.memory_bytes).to_equal(2000)
        expect(allocation.memory_cap_bytes).to_equal(2000)
        expect(allocation.below_recommendation).to_equal(true)

    it "should queue one byte below the memory floor despite spare CPU":
        step("Offer enough CPU but one byte less than the declared memory minimum")
        val plan = plan_host_placement_v1(placement_request(), [placement_host("memory-short", [], 8000, 1999)]).unwrap()
        expect(plan.selected_index).to_equal(-1)
        expect(plan.offers.len()).to_equal(0)
        expect(plan.rejected.len()).to_equal(1)
        expect(plan.rejected[0].reason).to_equal("insufficient-memory-minimum")

    it "should keep the only uncertain GPU unavailable after reducing CPU and memory requests":
        step("Keep the single exclusive GPU charged while CPU and memory are abundant")
        var host = placement_host("single-gpu", ["gpu-0"], 8000, 24000)
        host.ledger.reservations = [placement_gpu_reservation(["gpu-0"], HostReservationStateV1.Uncertain)]
        var request = placement_request()
        request.profile.gpu_required = true
        request.gpu_mode = "whole-exclusive"
        val original = plan_host_placement_v1(request, [host]).unwrap()
        expect(original.selected_index).to_equal(-1)
        expect(original.rejected[0].reason).to_equal("exclusive-gpu-unavailable")
        step("Reduce only CPU and memory while preserving the required exclusive device claim")
        request.profile.cpu = ResourceAmountRangeV1(minimum: 500, recommended: 500, preferred: 500, limit: 500)
        request.profile.memory = ResourceAmountRangeV1(minimum: 1000, recommended: 1000, preferred: 1000, limit: 1000)
        val reduced = plan_host_placement_v1(request, [host]).unwrap()
        expect(reduced.selected_index).to_equal(-1)
        expect(reduced.offers.len()).to_equal(0)
        expect(reduced.rejected[0].reason).to_equal("exclusive-gpu-unavailable")
        val remaining = host_available_capacity_v1(host.ledger).unwrap()
        expect(remaining.cpu_millis).to_equal(7000)
        expect(remaining.memory_bytes).to_equal(23000)
        expect(remaining.exclusive_devices.len()).to_equal(0)
```

</details>
