<!-- codex-design -->
# Simple Container host admission and provider design

Status: proposed, 2026-09-26. Shared foundation names are fixed by the parallel lane agreement. Native provider activation depends on user-selected privilege requirements and live target-host evidence.

The public entrypoint is Simple Container. The Linux `engine` setting is a
provider-internal compatibility choice today; `podman` is its current default,
not a promised cross-host dependency. A future in-tree Simple Linux provider
must be selected through an explicit provider ID and the same capability,
identity, lifecycle, and SDN contracts. Switch the Linux default only after
source-matched live parity and negative tests; keep Podman selectable for
existing OCI workloads. Windows uses its own HCS leaf and never routes through
a Linux Podman VM.

## Value contract

| Value | Fields |
|---|---|
| `ContainerHostRequirementV1` | `host_os`, `guest_os`, `isolation_class`, `require_unprivileged_client` |
| `ContainerHostCapabilityV1` | `host_os`, `guest_os`, `provider_id`, `isolation_class`, `client_privilege`, `admin_setup`, `launch_capable`, `reason` |

Use canonical host identifiers agreed by implementation and exact comparisons. Reject unknown host/isolation/privilege values, empty provider identity, mismatched execution OS, unavailable client and a false launch capability. Admit `native-container` for Linux, Windows, FreeBSD, and SimpleOS or `native-sandbox` for macOS when a trusted provider proves it. Reject `virtual-machine` for Simple Container. Successful `container_host_admission_reason_v1` returns `""`; every refusal returns a concrete nonempty reason. Pure admission validates an observation supplied by a trusted owner; it does not prove provenance or perform a native probe.

`admin_setup` is a boolean and is independent of `client_privilege`: an ordinary client can depend on administrative setup. A delegated launch requires the provider owner to validate scoped authorization before setting `launch_capable`; an SDN document cannot supply this proof. The controller additionally enforces strict rootless policy if selected, because `require_unprivileged_client` only requests no administrator action per run and therefore admits an authorized delegated client. A zero-admin-ever policy also excludes `admin_setup: true`.

## SDN receipt

The capability table header is `container_host_capability |field, value|`; its first data row is `schema, simple-container-host-capability-v1`. Emit one row per named field, in deterministic order. The build-host handoff uses a distinct schema with the same SDN table grammar. SDN is the external configuration/receipt authority; a native runtime may require generated API or OCI encodings internally, but those are adapter outputs rather than competing user configuration.

The codec must bound total document size and field size before expensive parsing, reject duplicate/missing/unknown fields, reject invalid boolean and enum tokens, and reject malformed quoting or escapes. Strings containing delimiters, quotes, newlines or backslashes must round-trip through the canonical SDN escaping rules. Do not split escaped table rows on a bare comma. Exact numeric bounds and codec helper names are owned by the SDN implementation and must be recorded with its executable tests before acceptance.

Keep human diagnostics out of machine stdout. Machine failures must use a nonzero exit and a bounded diagnostic; command discovery failure cannot produce a launch-success receipt. Preserve the existing build-host script's human mode. A build preflight success cannot be reused as container lifecycle evidence.

## Lifecycle algorithm

1. The controller freezes host/guest/isolation and the selected execution policy. The provider discovers facilities without mutation and reports capability.
2. Validate the exact capability request and current caller authorization. Resolve a host-compatible immutable workload fixture; reject incompatible architecture or kernel/image metadata before native create.
3. Persist or retain the attempt identity before issuing create: pod UID, attempt, provider generation, operation ID, engine and boot identity. The native ID must be supplied by the actual provider, never a user-chosen PID.
4. Invoke the provider with argument vectors or typed native APIs. Validate native outcomes and only then publish `RuntimeOperationV1` state. Timeout, rejected authorization and uncertain native completion do not advance the common model.
5. Obtain exit code from the bound native workload. Capture bounded output/logs only if supported. The owner commits the observation after checking full identity; discard stale results.
6. Destroy only the bound workload and verify native absence. On partial creation or cancellation, reconcile that attempt before retrying. Recovery is optional and must not be advertised without an identity-safe durable journal.

Existing hosted phase transitions are prepared/create/start/wait/stop/destroy; idempotent handling follows `runtime_transition`. SimpleOS currently exposes a combined managed launch from unknown to running and a scheduler-authoritative exit reconciliation. It shares envelopes without claiming a fabricated create phase, destroy API, logs or durable recovery. Future parity must add real mechanisms and tests.

## Provider constraints

Linux uses the existing OCI adapter; its already-dirty implementation belongs to another lane. Rootless tests must inspect the actual invoking UID, effective provider mode, UID mapping and required isolation/resource facilities. Engine branding alone is insufficient.

Native Simple Linux follow-up: own user namespaces, cgroup v2 delegation,
filesystem/network setup, immutable executable or image admission, bounded
output, start identity, cancellation, and fresh exact-ID absence behind a new
Linux leaf. Do not change the default until these behaviors match the selected
requirements in live non-root fixtures and the distributed-build worker can
consume its capability without changing its shared admission contract.

Windows requires a Windows image and explicit process isolation for the native-container route. A proposed HCS adapter owns compute-system and process handles and records the native compute identity. Service discovery without authorized lifecycle execution remains blocked. Hyper-V/VM fallback is rejected.

FreeBSD requires a jail-backed provider, FreeBSD guest compatibility, identity-bound jail operations and explicit storage/network prerequisites. A configured ordinary client can be delegated; describing it as Linux-style rootless would be incorrect. No Windows/FreeBSD broker is implemented or selected by this document.

The macOS route must launch a macOS program directly through a signed App Sandbox helper and an owned native process lease. It shares identity, lifecycle, and SDN receipt values with SimpleOS, whose kernel provider keeps scheduler authority. A Mac contract fixture or process launch alone is not live sandbox evidence; verify actual entitlements, denied host access, native exit, and cleanup.

Mac detail design and same-owner limitations are in
[native_macos_simple_container.md](native_macos_simple_container.md).

## Limits and observability

Providers own finite command timeouts, output byte caps, concurrent operation limits and cleanup deadlines. Select numeric operational limits with NFR requirements before live rollout. Log operation/attempt identifiers, duration and refusal reason without secret environment values. Mutable state remains serial per workload; independent workloads may execute concurrently and return copied bounded results to their controller. No global container scan or full-tree reread belongs in the lifecycle hot path.

The [test plan](../03_plan/sys_test/simple_container_cross_host.md) separates pure contract, script preflight and live provider gates. Follow [architecture ownership](../04_architecture/simple_container_cross_host.md) when adding platform leaves.
