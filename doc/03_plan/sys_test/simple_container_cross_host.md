<!-- codex-design -->
# Simple Container cross-host test plan

Status: proposed acceptance plan, 2026-09-26. AC identifiers below are design criteria, not user-selected REQ identifiers. Merge the selected requirements' IDs before claiming complete requirement coverage. Platform and privilege selection is pending.

## Evidence stages

| Stage | What a PASS proves | What it cannot prove |
|---|---|---|
| Contract | Pure admission, codec validation and lifecycle model behavior | Host availability, real isolation or rootless execution |
| Preflight | Installed/configured tools and observed host prerequisites | Successful native launch or cleanup |
| Live lifecycle | Actual create/start/exit/destroy on the recorded target | Untested hosts or optional recovery/log capability |
| Isolation/authority | Tested denial, identity binding and boundary enforcement | Broader privileges or controls not exercised |

A missing host/provider is BLOCKED with a concrete reason. Required missing evidence fails the release gate; it is never a passing placeholder or an unexplained skip. Mocked command output belongs to contract evidence only.

## Criteria and scenarios

| Criterion | Required assertions | Evidence |
|---|---|---|
| AC-01 exact routing | Correct host/guest/class admitted; each mismatch and unknown value rejected; VM rejected for native request | Pure unit results |
| AC-02 honest privilege | Unavailable and undiscovered launch rejected; strict policy rejects delegated; delegated requires current scoped authorization; setup requirement retained | Unit plus selected-policy live authority test |
| AC-03 SDN integrity | Round-trip every field and escaped delimiter; reject duplicate, missing, unknown, oversized and malformed fields; separate build/capability schemas | Codec unit results and script stdout/stderr/exit capture |
| AC-04 native lifecycle | Actual native identity exists after create, executes unique output marker, reports chosen nonzero exit, disappears after destroy | Native provider receipt and bounded execution capture |
| AC-05 cleanup/identity | Reject unrelated native identity, generation and boot mismatches; cancellation/timeout leaves recoverable state; repeated destroy safe; failed create cleanup checked | Contract plus native negative tests |
| AC-06 isolation | Workload cannot read an unmounted host sentinel or obtain denied authority; required network/resource policy independently observed | Native host observations |
| AC-07 SimpleOS contract | Managed launch reaches scheduler; bound zombie exit reconciles; foreign PID/stale identity rejected; logs/recovery report unavailable | Existing/new SimpleOS executable evidence |
| AC-08 macOS scope | Fixture/build receipt identifies Darwin; capability rejects native launch; foreign guest fixture cannot masquerade as host support | Local fixture and contract results |

## Native matrix

Linux runs under a non-root host UID with the selected rootless runtime. Record effective runtime mode and UID mapping, then execute AC-04 through AC-06. Exercise missing namespace/id mapping and unavailable resource facilities as explicit denials. Do not infer rootless support from successful `--version`.

Windows Server records host build, native runtime and compatible Windows image. Use native process isolation and ordinary client credentials for a delegated option; verify a second unauthorized identity cannot create, inspect or destroy the workload. Under strict rootless policy an unavailable native route must stay blocked. Reject Hyper-V/VM fallback.

FreeBSD records release, jail/OCI runtime, guest compatibility, storage/network configuration and actual jail identity. Verify authorized and unauthorized callers according to the selected privilege option, then run lifecycle/cleanup and host-sentinel denial. Administrative provisioning is recorded independently from launch client identity.

SimpleOS reuses `SimpleOsContainerProviderV1` managed launch and scheduler reconciliation scenarios. Preserve its advertised optional capability limits. macOS runs the container fixture and shared contracts; it cannot satisfy live Linux, Windows or FreeBSD gates.

## SPipe shape and artifacts

Use shared helpers `setup_host_capability_fixture_v1` and `check_host_capability_receipt_v1`. Primary manual steps are `step("inspect host capability")`, `step("create isolated workload")`, and `step("observe exit and destroy")`. Setup expands through `@inline`/`@prev`; detailed malformed-input matrices may be folded. Missing live execution must fail with `fail("host capability unavailable")` or an equivalent explicit blocked outcome.

Planned system spec: `test/03_system/app/container/feature/simple_container_cross_host_spec.spl`; mirrored manual: `doc/06_spec/03_system/app/container/feature/simple_container_cross_host_spec.md`. These are proposed locations, not artifacts created by this documentation lane. Contract unit specs are owned by the core/SDN lanes. Use built-in matchers and assert real identities, exact reasons, exit status and artifact contents; no constant-true, empty-body or `pass_todo` scenarios.

Capture bounded `exec`, `protocol`, `log` and `artifact` evidence under `build/test-artifacts/<spec-relative-path>/`. Each receipt must bind target OS, guest OS, provider/version, isolation, privilege observation, operation identity, stage and result. Native image fixtures must be immutable and contain a deterministic output/exit payload; generation must not contact arbitrary services. Separate preflight data from observed workload evidence.

Generate manuals using the admitted self-hosted `spipe-docgen` path, review readable user flows and require zero stubs. Do not create executable specs in `doc/06_spec`. Measure warm preflight, lifecycle latency and peak RSS once per selected NFR fixture; do not invent compliance while thresholds are pending.

## Completion gate

Root owns merge; Astra performs final review. This design lane has no additional sidecars. Run each accepted criterion once after its final relevant change, with at most three fix/verify cycles. Record blocked native hosts honestly. Shared-library changes also require the repository's compiler/lib/MCP/LSP checks and runtime/native smoke gates; foundation unit PASS alone cannot qualify a cross-host release.
