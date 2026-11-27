# Podman probe version eligibility evidence

Source-only; compiler/spec/native executions NOT_RUN. Root reports host Podman4.9.3 rootless/systemd/cgroupv2/netavark/overlay on arm64. That is the default invocation, not the independently configured cgroupfs/vfs/new-root profile. No worker upgrade, package change, provisioning or runtime campaign occurred.

| Closed operation | v5.2.5 source | v4.9.3 source | Narrow result |
|---|---|---|---|
| wait -- fullID | [source](https://github.com/podman-container-tools/podman/blob/v5.2.5/cmd/podman/containers/wait.go), blob e559c0a1e4d77b8a3f233a650999860eb24bcb59 | [source](https://github.com/podman-container-tools/podman/blob/v4.9.3/cmd/podman/containers/wait.go), blob da038db250e19c93f8a08b0a6e6225ed4e711e0a | Both print actual per-ID payload ExitCode; helper exit and payload exit remain distinct. |
| logs -- fullID | [source](https://github.com/podman-container-tools/podman/blob/v5.2.5/cmd/podman/containers/logs.go), blob 3b1f25b09ca0065f9a0c867a52d1a92911fa834e | [source](https://github.com/podman-container-tools/podman/blob/v4.9.3/cmd/podman/containers/logs.go), blob 2069281073035e5dfb053844e2733343412e7e5e | Both default Follow=false, Tail=-1 and send actual stdout/stderr to respective writers; upper owns bounded combined capture. |

These two commands have minimum syntactic eligibility in both audited versions. This is NOT a general4.9.3 support floor, not a qualified runtime version range, and not qualification of all required Create/Pull/inspect42/image/config/runtime/security/cgroup/rootless/storage behavior. No earlier versions were audited. Missing/unknown actual outputs still refuse; no legacy fallback.

The existing full profile requires explicit --remote=false, --log-level=error, --cgroup-manager=cgroupfs, exact protected --root/--runroot, --storage-driver vfs and exact --tmpdir. Wait/Logs retain that complete genuine bound prefix, pinned provider/broker image/security/helper budget and closed full native ID. Default host systemd/overlay info cannot attest that selected profile; the profile-specific actual observation is separately required. Network default netavark is not evidence for the explicitly network=none created workload.

Current executable selection contract: LinuxFreshEpochProfileV1 has providerExecutable/providerExecutableSha256/providerPolicyDigest; actual Native retains root-controlled executable ancestry, hashes the exact image and rejects file capabilities, mode/owner/root changes. LinuxOciEnginePolicyV1 has mode/executable_path/expected_uid/graph/run/driver/options and NO expected_version/minVersion field. LinuxOciEngineObservationV1 includes engine_version in its identity; match checks only nonempty and length<=256. Thus an administrator can select a separately qualified binary through exact protected path/hash/profile/policy bytes, but cannot claim the schema itself enforces a5.2.5 string. A version string is not capability. Changing from the existing pin requires an explicit separately approved/provisioned fixture; no worker implicitly changes the profile or blesses4.9.3.

An isolated binary used by this fresh Native profile must also meet its actual root-owned protected ancestry and approved admin runtime/configuration assumptions. A caller-owned /tmp download path is not automatically an eligible executable root. Root may obtain/qualify a separate binary and choose the real profile; workers do not install/elevate or mutate the running host here.

Runtime qualification remains NOT_RUN/NOT_COVERED for both full profiles. The new cohort observer also requires no remaining service/subuid/unknown partition processes other than the original Host; real pause/conmon/hidepid/races may prevent eligibility and must not be waived based on a version label.

