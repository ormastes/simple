# Controller dispatch dependency preservation

## Scope and ownership

Base: bff1db6668e, work/orchestrator-local-dispatch-20261107. This commit preserves
the necessary pure placement, immutable assignment, desired-state fence and
signed execute packet dependencies for actual external controller-to-host OCI
dispatch. It does not complete the service. Astra owns app/store composition;
host owns authenticated execution and provider effects. TaskRunnerV1 retains
DAG readiness and parent result acceptance. No new scheduler or journal exists.

The user-directed campaign selected the signed dispatch slice. These contracts
preserve previously unmerged work from /home/yoon/dev/simple rather than importing
the broad app, AgentSession policy/image paths or historical verification claims.

## Provenance

Original SHA-256 snapshots from main's unmerged source on 2026-11-07:

| Source | SHA-256 |
|---|---|
| `src/lib/common/contracts/orchestration/placement_v1.spl` | `f25130b46e1a50691f3996507fe8fe7fd8d22cc950c3b4876c097ecb392b4f8f` |
| `src/lib/common/contracts/orchestration/assignment_v1.spl` | `e5851abca61fa7aa5a2fdadb8d06809afbbcb4983c90c0673dc2c0ca98fb876f` |
| `src/lib/common/contracts/orchestration/workload_fence_v1.spl` | `7ccffed8db63f79892c0d9498150ea5e36a74dc5bf66eabe7b197d803e952060` |
| `src/lib/common/contracts/orchestration/workload_fence_codec_v1.spl` | `a3d66899ed1416510bc8ac004a5c713119d384fa2f70eb64e01763ef36c3147c` |
| `src/lib/common/contracts/orchestration/linux_launch_plan_v1.spl` | `c08a5867fddef5375589865b252716de11202e178370eec81bc4d7d3e43bf64f` |
| `src/lib/common/contracts/orchestration/linux_launch_plan_codec_v1.spl` | `3ef2527323ae9b9144775cd5ee4abab6048e30fba30990121a3ec500fca312d4` |
| `src/lib/common/contracts/orchestration/host_prepare_response_v1.spl` | `9cd8835a05aa24a41a311b2084445e5d2e72f8fca6d499afaa36a055a14fb8aa` |
| `test/03_system/app/orchestrator/feature/placement_spec.spl` | `36773fcb86e03e7088d5fe622901f54a2977eeddeff488b6a50838ba3a3afb31` |
| `test/fixtures/orchestration/placement_native_probe.spl` | `07f346f771cdc74fd5b0aedc1641cbececf2afeef5f984009367f2b9b0ce7e80` |
| `test/02_integration/lib/daemon_sdk/assignment_commit_spec.spl` | `0d1a5c70f638a52269c6393171fecb36e18776d657a98667c86e0645d51a1c49` |

The seven original contracts and placement spec/probe are copied byte-for-byte.
New controller_workload_fence_spec/native probe adapt the pure bind/cancel and
retirement assertions from assignment_commit_spec, add canonical restore and
replay negatives, and compose placement -> intent -> host operation -> immutable
assignment -> workload fence without mutating the original host ledger.
HostExecuteRequestV1 and its envelope-only spec/probe are new agreed shared work.
The resource-profile foundation and host capacity/reservation/V2 journal/daemon
foundation are already present in this branch; no historical .spipe state copied.

## Integrity and authority boundaries

Placement plans expose resource caps and the selected host ledger fence. They
reserve nothing and cannot bypass current host admission. A workload binds once;
exact replay is idempotent, cancellation is sticky, and a replacement requires
future evidence-checked retirement. Heartbeat loss, restart and unknown outcomes
are never permission to replace an active assignment or release capacity.
Canonical assignment objects bind the exact host intent and V2 envelope hashes.
Receipt digests establish integrity, not authenticated host provenance.

HostExecuteRequestV1 contains original host_reservation_v1 operation, intent,
prepared receipt, full scoped launch plan, request_bytes and untrusted signed
execution grant/approval. Existing operation/signature/receipt codecs are reused.
The boundary rejects legacy blank host scope, mismatched physical host/boot/
provider generation/service scope, incorrect plan digest, receipt tampering,
unknown/duplicate fields and noncanonical envelope syntax.

The request body limit is 1048576 UTF-8 bytes and total packet limit2097152 bytes,
measured with common.string_core.str_len. Nested escaping can cause a valid
individual body to exceed the total packet budget; the packet fails closed with
no truncation. The opaque request must be nonempty strict canonical SDN; this is
not provider-schema admission. Multibyte boundary tests cover these byte budgets.

linux_oci_request_digest_v1 hashes a versioned preimage of field hashes/counts,
not raw retained request bytes, and excludes operation_id. Common cannot import
provider schema and deliberately does not trust an embedded requestDigest.
Before ANY execution effect the host must decode the canonical retained provider
request, recompute the semantic digest, match plan/request/intent allocation and
operation identity, and verify action-specific signed grant AND approval against
protected local snapshots and current clocks. Zero signatures and opaque fixtures
in envelope tests demonstrate data shape only and grant no authority.

## Dependency closure and validation limits

These sources directly reuse existing common build_manager contracts/codec,
crypto.sha256, distributed_control_v2/codec, distributed_authority_v2/codec,
sdn value/parser/encode/strict_v1/strict_types_v1 and string_core. Host-owned
host_capacity_v1 and host_reservation_codec_v1 and previously landed resource_v1/
profile_v1 provide remaining domain dependencies. host_prepare_response_v1 is
imported under delegated host ownership. No provider, app, task_runner, mutable
workload_store, daemon listener or journal import is added by this pure slice.

Specs: placement_spec, controller_workload_fence_spec, host_execute_request_spec.
Matching manuals are authored and explicitly NOT_RUN, with no historical PASS.
Native probes are diagnostic fixtures, not admitted evidence. Admitted SSpec,
SPipe generation/maintenance, coverage, core/MCP/LSP smoke and live Podman are
NOT_RUN. Static source/hash/import checks do not qualify runtime execution.
Actual acceptance still requires an external controller process invoking the
host service and an independent provider nonce/native-identity inspection oracle.
Missing live Podman means that full-system acceptance is BLOCKED.

Sol owns this dependency implementation; Astra performs exact-head review and
owns app/store integration; root coordinates builds and landing. Additional
sidecars: N/A. No build is performed for this dependency commit.
