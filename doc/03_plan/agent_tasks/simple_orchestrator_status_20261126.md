# Simple Orchestrator release progress and remaining work

Snapshot taken 2026-11-26 (Asia/Seoul) against `release/1.0.0` at
`7035e24b2679a83499cd6c841514b75b5cdd9c72`. Update this plan when a gate
changes state and record the source revision and supporting evidence.

## Follow-up — 2026-11-26

- The Windows Docker provider landed a live process-isolation smoke test
  through `WindowsDockerRuntimeProviderV1`. The PR reports one passing run on
  Windows build 26300 with the pinned Nano Server LTSC 2025 image using an
  opt-in hosted interpreter path. The shared `WindowsSimpleContainerAdapterV2`
  and enrolled Host service still need live qualification with a native boot
  identity. Native AOT execution, terminal and resource enforcement, and the
  Windows 11 23H2/Server Core 2022 fixture remain separate qualification gates.
  [Windows Docker live run](https://github.com/ormastes/simple/pull/11946)
- The signed helper-authorization spec for **AT-HOST-05** is in a draft PR
  with a passing structural check. If expiry wins, late authorization cannot
  issue a lease. If execution wins, expiry and replay cannot release the
  active reservation. Native
  execution is `NOT_RUN`. Concurrent fault injection and proof at the
  provider launch boundary remain open. [Signed helper spec](https://github.com/ormastes/simple/pull/11942)
- The provisioning draft also passed its structural check. Its native matrix
  was skipped, so retain the same four gates below. Once the admitted native
  runner is published, the signed helper spec can run using its private
  journal fixture while the operator prepares the installed-host fixture.
  Capture native receipts against each PR's verified head.

## On the release branch

- Linux has an OCI lifecycle provider wired into CI. The Linux Host V4 service
  can open an installed anchor and handle associated prepare/execute through
  the smux owner. Live signed provisioning and a workspace-backed interactive
  Podman session still need separate runtime evidence.
  [Linux Host V4 startup](https://github.com/ormastes/simple/pull/9745)
- Five modern SSpec suites are merged, with 69 registered source cases across
  daemon dispatch, placement, SDN resources, smux leases and build-runner
  remote reports. The count describes the source inventory. Native results
  for the acceptance run are pending.
  [Daemon](https://github.com/ormastes/simple/pull/9670),
  [placement](https://github.com/ormastes/simple/pull/9671),
  [SDN](https://github.com/ormastes/simple/pull/9672),
  [smux](https://github.com/ormastes/simple/pull/9673),
  [remote reports](https://github.com/ormastes/simple/pull/9674)
- The Stage 2 `MirType.f32` linker fix is merged. The handoff records an
  admitted Stage 2 compiler for its pinned build. The source-matched full
  verification CLI and SSpec runner receipt were still outstanding when
  checked. [Linker fix](https://github.com/ormastes/simple/pull/11873)

## Signed Linux provisioning — four remaining gates

| Gate | Responsible role | Evidence required to close |
| --- | --- | --- |
| 1. Qualify the test runner | Bootstrap owner | Publish the source-matched verification CLI and admitted LLVM AOT SSpec runner/runtime receipt for the queued source revision. |
| 2. Provision a dedicated fixture | Linux host operator | Supply the approved controller, signed enrollment input, protected install and dispatch roots, key and output stores, and approver. Keep credentials and host details outside the repository. |
| 3. Execute acceptance and verify the manuals | Orchestrator verification | Run the signed issuer, enrollment, association and Host currentness cases, including stale epoch or wrong-host refusal. Run the installed-host flow through issue, provision, exact retry and startup. Retain the native runner log and evidence, verify the matching SSpec manuals, and record failed or blocked cases separately. |
| 4. Land and confirm the result | Provisioning PR owner | Review the verified head, resolve findings, merge into `release/1.0.0`, and confirm the merge on the remote branch. |

Source review covers the latest recorded three-file increment of draft
[PR #11928](https://github.com/ormastes/simple/pull/11928) at
`aef677005b88e7e0401668a9f36dc196306a54fb`. Native acceptance for that head
is `NOT_RUN`. A separate installer SSpec change exercises altered-signature
refusal and verifies that exact retry preserves the claim and root manifest.
Its source has been reviewed locally and remains unmerged and `NOT_RUN`.
Coordinate the two changes so the installed-host fixture and cleanup ownership
are exercised at both entry points.

Use the repository's `scripts/bootstrap/run-native-aot-suite.shs` for the
pinned first pass, with explicit LLVM AOT and at most five cores in total.
Run the pure contract cases when the runner is ready. The installed-host case
also needs the dedicated fixture. Record the source revision, compiler and
runner identities, executed cases, outcomes and manual verification beside
the corresponding SSpec inventory.

**Planning estimate:** allow 1–2 working days for the provisioning acceptance
and merge after gates 1 and 2 close, assuming the first pass exposes no
substantial defect. Runner publication and fixture availability have no
confirmed dates.

## Remaining release acceptance

The original release plan has 39 acceptance obligations. The latest source
trace recorded eight with exact test annotations and 31 needing semantic
mapping. Map the remaining obligations to concrete assertions and evidence,
then add only the missing scenarios. Record platform availability per
obligation. The native run must establish the verified pass count and any
remaining failures or gaps.

| Workstream | Next evidence to collect |
| --- | --- |
| Shared daemon, SDN and placement | Run the merged suites and check response loss, exact daemon custody, reservation expiry and replay, and recovery under storage or host failure. |
| Simple Container and host | Qualify the Linux Podman route through the shared API, including workspace, limits, exec/TTY and exact cleanup. Exercise Windows Docker process isolation through the V2 adapter and enrolled Host service. |
| Live remote enrollment, smux and Caret | Exercise authenticated enrollment, SDN-backed placement, one bound terminal stream, detach/reconnect, cancellation races and exact termination with workspace retention. |
| Build/test integration | Run remote result verification and incomplete-result refusal alongside local runner regressions. Confirm that the parent controls verdicts and cache publication. |
| Optional providers | Keep FreeBSD, Apple Linux VM and Kubernetes in separate qualification lanes with their own fixtures and capability evidence. |

The [remote completion plan](simple_orchestrator_remote_completion.md) tracks
operator prerequisites, platform blockers and Todo DB rows. Re-estimate the
full release once the trace is resolved and the platform owners have confirmed
fixtures. The estimate above covers signed Linux provisioning.
