# Resource-profile foundation

## Scope and authority

Preserve the existing strict resource decoder and pure ResourceProfile allocation
logic as the shared foundation for host capacity and controller placement.
The user-directed parallel campaign selected this foundation; this is no new
requirement selection. Configuration and allocation proposals authorize no host
execution. TaskRunnerV1 continues to own DAG readiness and parent result acceptance.
No scheduler, daemon, operation journal, capacity ledger or provider is introduced.

`resource_v1.spl` checks decimal accumulation before multiply/add, whole-core CPU
scaling before multiplying by 1000, and memory suffix scaling before multiplying.
Every overflow returns the existing -1 quantity sentinel. The profile decoder
parses through `parse_resource_document`, which rejects parser issues including
duplicate keys, then validates the shared envelope and the known profile fields.
Value decoder callers must preserve that strict parser boundary and source spans.
Existing Pod/Deployment decoding delegates to the same boundary and retains its
legacy root diagnostic paths; nested Deployment errors use the supplied prefix.

The profile requires 0 <= min <= recommend <= prefer <= limit for CPU and memory.
Missing optional amounts inherit the preceding amount. Normal proposals target
recommend; explicit preference targets prefer. Capacity below either minimum is
refused, and effective caps equal selected allocations rather than declared limits.
GPU intent remains unresolved until the host-owned device claim is validated.
Directly constructed typed profiles receive the same order validation.

## Provenance

Destination base: `671d5545201c5c5bc73ea0ddaf0db0f143218d44`
(`release/1.0.0` at isolated worktree creation). Sources were read from the shared
`/home/yoon/dev/simple` tree on 2026-11-07. They were unmerged work: resource_v1
was tracked/modified; profile and the fixture were untracked. The whole resource
file is preserved, including the shared envelope/value decoder needed by profile.
No unrelated dirty source or database records were imported.

Original SHA-256 identities:

| Source | SHA-256 |
|---|---|
| `src/lib/common/contracts/orchestration/resource_v1.spl` | `94eb3d3f16a9a45b0bd6cb96b151871c169a3f8dbf96f0dcfd3617df0a61a9ca` |
| `src/lib/common/contracts/orchestration/profile_v1.spl` | `39cf4f6514c57a449802f238ca303379424f33dc428811bcd1b551b32d1aaba6` |
| `test/fixtures/orchestration/agent_cpu_profile.sdn` | `b711a21aba68a0ccf538aaaf615abc573de79e5204a81465730fa22771b30423` |
| adapted `test/03_system/app/orchestrator/feature/resource_profile_spec.spl` | `861b79b46cd0b1ccb776ddc5769b93ffe929260764ab6f8905c605f5268bb850` |

## Focused verification

`test/03_system/app/orchestrator/feature/resource_profile_foundation_spec.spl`
uses the profile decoder directly and excludes ResourceList/unified loader cases.
It adds exact i64, CPU multiplication and binary/decimal memory scaling boundaries,
duplicate-key provenance and invalid typed memory ranges to the original real
profile assertions. Its profile fixture is `agent_cpu_profile.sdn`; the existing tracked
`echo_deployment.sdn` also verifies nested Deployment selector error paths and
source coordinates through the shared value decoder. A standalone
`resource_profile_foundation_native_probe.spl` includes a real indented nested
numeric 10000 assertion, quantity boundaries and direct profile allocations.
That probe remains diagnostic-only and NOT_RUN until a build slot is granted.

Runtime verdict: **NOT_RUN**. No admitted self-hosted runner is available and no
build slot was granted for this preservation change. No coverage percentage,
SPipe generation, runtime PASS, compiler/MCP/LSP smoke, production readiness or
release qualification is claimed. The matching manual is authored, not generated.
Static diff/provenance checks do not substitute for executing the spec.

Ownership: Sol worker implements this exact foundation; Astra orchestrator lead
reviews its exact commit before host/controller consumers adopt it. Root owns
scarce builds, integration and landing. Additional sidecars: N/A.
