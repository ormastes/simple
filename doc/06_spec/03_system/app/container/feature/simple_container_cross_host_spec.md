# Simple Container Cross Host Specification

> Tests covering simple container cross host, AC-01 exact host guest and isolation routing, AC-02 honest privilege reporting, AC-03 SDN capability receipt integrity, AC-05 lifecycle oracle cleanup and identity, AC-08 macOS scope, AC-04 AC-06 AC-07 native live gates.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Container Cross Host Specification

## Scenarios

### simple container cross host

### AC-01 exact host guest and isolation routing

#### should admit exact native routes for every supported host

- Inspect host capability for each exact host/isolation pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect host capability for each exact host/isolation pair")
expect(check_host_capability_receipt_v1("linux",
    CONTAINER_ISOLATION_NATIVE_V1, CONTAINER_CLIENT_PRIVILEGE_USER_V1,
    true, exact_requirement_v1("linux", CONTAINER_ISOLATION_NATIVE_V1))).to_equal("")
expect(check_host_capability_receipt_v1("freebsd",
    CONTAINER_ISOLATION_NATIVE_V1, CONTAINER_CLIENT_PRIVILEGE_DELEGATED_V1,
    true, exact_requirement_v1("freebsd", CONTAINER_ISOLATION_NATIVE_V1))).to_equal("")
expect(check_host_capability_receipt_v1("windows",
    CONTAINER_ISOLATION_NATIVE_V1, CONTAINER_CLIENT_PRIVILEGE_DELEGATED_V1,
    true, exact_requirement_v1("windows", CONTAINER_ISOLATION_NATIVE_V1))).to_equal("")
expect(check_host_capability_receipt_v1("simpleos",
    CONTAINER_ISOLATION_NATIVE_V1, CONTAINER_CLIENT_PRIVILEGE_USER_V1,
    true, exact_requirement_v1("simpleos", CONTAINER_ISOLATION_NATIVE_V1))).to_equal("")
expect(check_host_capability_receipt_v1("macos",
    CONTAINER_ISOLATION_NATIVE_SANDBOX_V1, CONTAINER_CLIENT_PRIVILEGE_USER_V1,
    true, exact_requirement_v1("macos", CONTAINER_ISOLATION_NATIVE_SANDBOX_V1))).to_equal("")
```

</details>

#### should reject every host guest mismatch and unknown value

- Present mismatched and unknown host guest and isolation values


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Present mismatched and unknown host guest and isolation values")
expect(check_host_capability_receipt_v1("linux",
    CONTAINER_ISOLATION_NATIVE_V1, CONTAINER_CLIENT_PRIVILEGE_USER_V1,
    true, exact_requirement_v1("windows", CONTAINER_ISOLATION_NATIVE_V1))).to_equal(
    "host-guest-os-mismatch")
expect(container_host_admission_reason_v1(
    setup_host_capability_fixture_v1("haiku", CONTAINER_ISOLATION_NATIVE_V1,
        CONTAINER_CLIENT_PRIVILEGE_USER_V1, true),
    exact_requirement_v1("haiku", CONTAINER_ISOLATION_NATIVE_V1))).to_equal(
    "host-capability-os-unsupported")
expect(container_host_admission_reason_v1(
    ContainerHostCapabilityV1(host_os: "linux", guest_os: "linux",
        provider_id: "p", isolation_class: "custom",
        client_privilege: CONTAINER_CLIENT_PRIVILEGE_USER_V1,
        admin_setup: false, launch_capable: true, reason: ""),
    exact_requirement_v1("linux", CONTAINER_ISOLATION_NATIVE_V1))).to_equal(
    "host-isolation-unsupported")
expect(container_host_admission_reason_v1(
    ContainerHostCapabilityV1(host_os: "linux", guest_os: "linux",
        provider_id: "p", isolation_class: "containerd",
        client_privilege: CONTAINER_CLIENT_PRIVILEGE_USER_V1,
        admin_setup: false, launch_capable: true, reason: ""),
    exact_requirement_v1("linux", CONTAINER_ISOLATION_NATIVE_V1))).to_equal(
    "host-isolation-unsupported")
```

</details>

#### should reject a VM for every native request

- Ask each native route to admit a virtual-machine capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask each native route to admit a virtual-machine capability")
for host in ["linux", "freebsd", "windows", "simpleos"]:
    expect(container_host_admission_reason_v1(
        setup_host_capability_fixture_v1(host, CONTAINER_ISOLATION_VM_V1,
            CONTAINER_CLIENT_PRIVILEGE_USER_V1, true),
        exact_requirement_v1(host, CONTAINER_ISOLATION_VM_V1))).to_equal(
        "virtual-machine-not-simple-container")
```

</details>

#### should reject native containers on macOS and sandbox on other hosts

- Cross the native-container and native-sandbox classes with the wrong host


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Cross the native-container and native-sandbox classes with the wrong host")
expect(container_host_admission_reason_v1(
    setup_host_capability_fixture_v1("macos", CONTAINER_ISOLATION_NATIVE_V1,
        CONTAINER_CLIENT_PRIVILEGE_USER_V1, true),
    exact_requirement_v1("macos", CONTAINER_ISOLATION_NATIVE_V1))).to_equal(
    "macos-native-container-unsupported")
expect(container_host_admission_reason_v1(
    setup_host_capability_fixture_v1("linux", CONTAINER_ISOLATION_NATIVE_SANDBOX_V1,
        CONTAINER_CLIENT_PRIVILEGE_USER_V1, true),
    exact_requirement_v1("linux", CONTAINER_ISOLATION_NATIVE_SANDBOX_V1))).to_equal(
    "native-sandbox-host-unsupported")
```

</details>

### AC-02 honest privilege reporting

#### should reject unavailable and undiscovered launch

- Inspect a capability whose launch is unavailable or unprobed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect a capability whose launch is unavailable or unprobed")
expect(check_host_capability_receipt_v1("linux",
    CONTAINER_ISOLATION_NATIVE_V1, CONTAINER_CLIENT_PRIVILEGE_UNAVAILABLE_V1,
    false, exact_requirement_v1("linux", CONTAINER_ISOLATION_NATIVE_V1))).to_equal(
    "host-launch-unavailable")
expect(check_host_capability_receipt_v1("linux",
    CONTAINER_ISOLATION_NATIVE_V1, CONTAINER_CLIENT_PRIVILEGE_USER_V1,
    false, exact_requirement_v1("linux", CONTAINER_ISOLATION_NATIVE_V1))).to_equal(
    "host-launch-unavailable")
```

</details>

#### should keep delegated routes explicit through provider probe translation

- Inspect FreeBSD and Windows delegated capabilities translated from probes
   - Expected: freebsd.client_privilege equals `CONTAINER_CLIENT_PRIVILEGE_DELEGATED_V1`
   - Expected: windows.client_privilege equals `CONTAINER_CLIENT_PRIVILEGE_DELEGATED_V1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect FreeBSD and Windows delegated capabilities translated from probes")
val freebsd = freebsd_jail_capability_from_probe_v1(
    FreebsdJailRuntimeProviderV1.scripted("ocijail", "/var/db/c",
        "boot-1", 1, true, "").probe(), true)
expect(freebsd.client_privilege).to_equal(CONTAINER_CLIENT_PRIVILEGE_DELEGATED_V1)
expect(freebsd.admin_setup).to_be(true)
val windows = windows_hcs_capability_from_probe_v1(
    WindowsHcsRuntimeProviderV1.scripted("server", "2025", "boot-1",
        1, true, "").probe(), true)
expect(windows.client_privilege).to_equal(CONTAINER_CLIENT_PRIVILEGE_DELEGATED_V1)
expect(windows.admin_setup).to_be(true)
```

</details>

#### should reject a strict unprivileged requirement when only delegated exists

- Require an unprivileged client where the provider reports unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require an unprivileged client where the provider reports unavailable")
expect(container_host_admission_reason_v1(
    ContainerHostCapabilityV1(host_os: "freebsd", guest_os: "freebsd",
        provider_id: "p", isolation_class: CONTAINER_ISOLATION_NATIVE_V1,
        client_privilege: CONTAINER_CLIENT_PRIVILEGE_UNAVAILABLE_V1,
        admin_setup: true, launch_capable: true, reason: ""),
    ContainerHostRequirementV1(host_os: "freebsd", guest_os: "freebsd",
        isolation_class: CONTAINER_ISOLATION_NATIVE_V1,
        require_unprivileged_client: true))).to_equal(
    "unprivileged-client-unavailable")
```

</details>

#### should never admit scripted provider probes as live evidence

- Translate a scripted Linux probe with live_source false
   - Expected: capability.reason equals `linux-oci-live-probe-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Translate a scripted Linux probe with live_source false")
val capability = linux_rootless_capability_from_probe_v1(
    RuntimeProbeV1(provider: "linux-oci-v1", engine: "podman",
        engine_present: true, healthy: true, launch_capable: true,
        privilege: "rootless", reason: "scripted"), false, "1000")
expect(capability.launch_capable).to_be(false)
expect(capability.reason).to_equal("linux-oci-live-probe-unavailable")
```

</details>

### AC-03 SDN capability receipt integrity

#### should round trip every field of a host capability receipt

- Format then parse a full capability receipt and compare each field
   - Expected: restored.host_os equals `capability.host_os`
   - Expected: restored.guest_os equals `capability.guest_os`
   - Expected: restored.provider_id equals `capability.provider_id`
   - Expected: restored.isolation_class equals `capability.isolation_class`
   - Expected: restored.client_privilege equals `capability.client_privilege`
   - Expected: restored.admin_setup equals `capability.admin_setup`
   - Expected: restored.launch_capable equals `capability.launch_capable`
   - Expected: restored.reason equals `capability.reason`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Format then parse a full capability receipt and compare each field")
val capability = setup_host_capability_fixture_v1("freebsd",
    CONTAINER_ISOLATION_NATIVE_V1, CONTAINER_CLIENT_PRIVILEGE_DELEGATED_V1,
    true)
val formatted = format_container_host_capability_sdn_v1(capability)
expect(formatted.is_ok()).to_be(true)
val parsed = parse_container_host_capability_sdn_v1(formatted.unwrap())
expect(parsed.is_ok()).to_be(true)
val restored = parsed.unwrap()
expect(restored.host_os).to_equal(capability.host_os)
expect(restored.guest_os).to_equal(capability.guest_os)
expect(restored.provider_id).to_equal(capability.provider_id)
expect(restored.isolation_class).to_equal(capability.isolation_class)
expect(restored.client_privilege).to_equal(capability.client_privilege)
expect(restored.admin_setup).to_equal(capability.admin_setup)
expect(restored.launch_capable).to_equal(capability.launch_capable)
expect(restored.reason).to_equal(capability.reason)
```

</details>

#### should reject malformed oversized and truncated receipts

- Parse corrupted receipts and require refusal, never a partial value


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse corrupted receipts and require refusal, never a partial value")
expect(parse_container_host_capability_sdn_v1("").is_ok()).to_be(false)
expect(parse_container_host_capability_sdn_v1("not-a-receipt").is_ok()).to_be(false)
val formatted = format_container_host_capability_sdn_v1(
    setup_host_capability_fixture_v1("linux", CONTAINER_ISOLATION_NATIVE_V1,
        CONTAINER_CLIENT_PRIVILEGE_USER_V1, true))
expect(formatted.is_ok()).to_be(true)
val receipt = formatted.unwrap()
expect(parse_container_host_capability_sdn_v1(
    receipt.substring(0, receipt.len() - 1)).is_ok()).to_be(false)
expect(parse_container_host_capability_sdn_v1(
    receipt + "\ninjected=row").is_ok()).to_be(false)
```

</details>

### AC-05 lifecycle oracle cleanup and identity

#### should advance only through the positively checked transition oracle

- Create isolated workload states through the shared pure oracle
   - Expected: created.status equals `RUNTIME_STATUS_OK`
   - Expected: created.state.phase equals `RUNTIME_PHASE_CREATED`
   - Expected: created.state.identity.native_id equals `jail-7`
   - Expected: started.state.phase equals `RUNTIME_PHASE_RUNNING`
   - Expected: waited.state.phase equals `RUNTIME_PHASE_EXITED`
   - Expected: waited.state.exit_code equals `3`
   - Expected: destroyed.state.phase equals `RUNTIME_PHASE_DESTROYED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create isolated workload states through the shared pure oracle")
var state = runtime_state_empty()
state.phase = RUNTIME_PHASE_PREPARED
state.identity = RuntimeIdentityV1(pod_uid: "pod-1", attempt: 1,
    provider_generation: 1, operation_id: "op-1", engine: "e",
    native_id: "", node_boot_id: "boot-1")
val created = runtime_transition(state, "create", "jail-7", -1, false)
expect(created.status).to_equal(RUNTIME_STATUS_OK)
expect(created.state.phase).to_equal(RUNTIME_PHASE_CREATED)
expect(created.state.identity.native_id).to_equal("jail-7")
val started = runtime_transition(created.state, "start", "jail-7", -1, false)
expect(started.state.phase).to_equal(RUNTIME_PHASE_RUNNING)
val waited = runtime_transition(started.state, "wait", "jail-7", 3, false)
expect(waited.state.phase).to_equal(RUNTIME_PHASE_EXITED)
expect(waited.state.exit_code).to_equal(3)
val destroyed = runtime_transition(waited.state, "destroy", "jail-7", 3, false)
expect(destroyed.state.phase).to_equal(RUNTIME_PHASE_DESTROYED)
```

</details>

#### should reject create without native id create from running and unforced destroy

- Present invalid transitions and require rejection without state advance


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Present invalid transitions and require rejection without state advance")
var state = runtime_state_empty()
state.phase = RUNTIME_PHASE_PREPARED
expect(runtime_transition(state, "create", "", -1, false).status).to_equal(
    RUNTIME_STATUS_REJECTED)
var running = runtime_state_empty()
running.phase = RUNTIME_PHASE_RUNNING
expect(runtime_transition(running, "create", "x", -1, false).status).to_equal(
    RUNTIME_STATUS_REJECTED)
expect(runtime_transition(running, "destroy", "x", -1, false).reason).to_equal(
    "running-workload-requires-force")
expect(runtime_transition(running, "bogus", "x", -1, false).reason).to_equal(
    "unsupported-transition-bogus")
```

</details>

#### should treat foreign identities as non-authoritative across providers

- Present a Windows identity to the FreeBSD admission check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Present a Windows identity to the FreeBSD admission check")
var identity = runtime_identity_empty()
identity.pod_uid = "pod-1"
identity.attempt = 1
identity.provider_generation = 1
identity.operation_id = "op-1"
identity.node_boot_id = "boot-1"
identity.engine = WINDOWS_HCS_ENGINE_V1
expect(windows_hcs_request_reason_v1(identity, "pod-1", "process",
    "sha256:" + "a".repeat(64))).to_equal("")
identity.engine = FREEBSD_JAIL_ENGINE_V1
expect(windows_hcs_request_reason_v1(identity, "pod-1", "process",
    "sha256:" + "a".repeat(64))).to_equal("windows-hcs-engine-mismatch")
```

</details>

### AC-08 macOS scope

#### should keep the macOS row a native sandbox capability only

- Inspect macOS capability admission for the sandbox class


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inspect macOS capability admission for the sandbox class")
expect(check_host_capability_receipt_v1("macos",
    CONTAINER_ISOLATION_NATIVE_SANDBOX_V1, CONTAINER_CLIENT_PRIVILEGE_USER_V1,
    true, exact_requirement_v1("macos", CONTAINER_ISOLATION_NATIVE_SANDBOX_V1))).to_equal("")
expect(container_host_admission_reason_v1(
    setup_host_capability_fixture_v1("macos", CONTAINER_ISOLATION_NATIVE_V1,
        CONTAINER_CLIENT_PRIVILEGE_USER_V1, true),
    exact_requirement_v1("macos", CONTAINER_ISOLATION_NATIVE_V1))).to_equal(
    "macos-native-container-unsupported")
```

</details>

#### should reject a foreign guest fixture masquerading as macOS support

- Present a linux guest under a macOS host capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Present a linux guest under a macOS host capability")
val capability = setup_host_capability_fixture_v1("macos",
    CONTAINER_ISOLATION_NATIVE_SANDBOX_V1, CONTAINER_CLIENT_PRIVILEGE_USER_V1,
    true)
val foreign = ContainerHostCapabilityV1(host_os: capability.host_os,
    guest_os: "linux", provider_id: capability.provider_id,
    isolation_class: capability.isolation_class,
    client_privilege: capability.client_privilege,
    admin_setup: capability.admin_setup,
    launch_capable: capability.launch_capable, reason: capability.reason)
expect(container_host_admission_reason_v1(foreign,
    exact_requirement_v1("macos", CONTAINER_ISOLATION_NATIVE_SANDBOX_V1))).to_equal(
    "host-guest-os-mismatch")
```

</details>

### AC-04 AC-06 AC-07 native live gates

#### should fail closed with explicit blocked reasons when no native host capability exists

- inspect host capability
   - Expected: freebsd_probe.reason equals `freebsd-jail-live-host-unavailable`
   - Expected: windows_probe.reason equals `windows-hcs-live-host-unavailable`
- create isolated workload
   - Expected: blocked.status equals `blocked`
- observe exit and destroy
   - Expected: blocked.reason equals `freebsd-jail-live-host-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("inspect host capability")
val freebsd_probe = FreebsdJailRuntimeProviderV1.new("linux", "",
    "/state", "boot-1", 1, true).probe()
expect(freebsd_probe.launch_capable).to_be(false)
expect(freebsd_probe.reason).to_equal("freebsd-jail-live-host-unavailable")
val windows_probe = WindowsHcsRuntimeProviderV1.new("linux", "server",
    "2025", false, "boot-1", 1, true).probe()
expect(windows_probe.launch_capable).to_be(false)
expect(windows_probe.reason).to_equal("windows-hcs-live-host-unavailable")
step("create isolated workload")
var state = runtime_state_empty()
state.phase = RUNTIME_PHASE_PREPARED
state.identity = RuntimeIdentityV1(pod_uid: "pod-1", attempt: 1,
    provider_generation: 1, operation_id: "op-1",
    engine: FREEBSD_JAIL_ENGINE_V1, native_id: "", node_boot_id: "boot-1")
val blocked = FreebsdJailRuntimeProviderV1.new("linux", "", "/state",
    "boot-1", 1, true).lifecycle_request_v1(state, "create", "pod-1",
    "freebsd:14.1")
expect(blocked.status).to_equal("blocked")
step("observe exit and destroy")
expect(blocked.reason).to_equal("freebsd-jail-live-host-unavailable")
# The positive native paths (rootless Linux podman lifecycle +
# isolation denial, FreeBSD jail identity, Windows process
# isolation, macOS signed sandbox launch, SimpleOS scheduler
# launch) require hosts and an admitted self-hosted CLI that are
# unavailable on this host; they are tracked as open evidence
# gates in doc/08_tracking/bug/seed_cfg_strip_kernel_closure_undefined_externs_2026-11-05.md
# and must never be reported as PASS without live receipts.
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/container/feature/simple_container_cross_host_spec.spl` |
| Updated | 2026-11-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple container cross host, AC-01 exact host guest and isolation routing, AC-02 honest privilege reporting, AC-03 SDN capability receipt integrity, AC-05 lifecycle oracle cleanup and identity, AC-08 macOS scope, AC-04 AC-06 AC-07 native live gates.
- simple container cross host
- AC-01 exact host guest and isolation routing
- AC-02 honest privilege reporting
- AC-03 SDN capability receipt integrity
- AC-05 lifecycle oracle cleanup and identity
- AC-08 macOS scope
- AC-04 AC-06 AC-07 native live gates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
