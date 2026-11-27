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

## Handoff — 2026-11-26 evening (Claude session)

All evidence below comes from the Rust seed interpreter. It is diagnostic only and is not native qualification.

- **Landed on `release/1.0.0`:**
  - #12035: endpoint routing reads only `schema`/`server_config` from a tolerant host file.
  - #12040: the V4 pane binding strict node budget is now 17. It was 16, so every valid binding was refused.
  - #12049: the helper-deadline and gateway-draft node budgets are fixed, and two stale private-import baseline rows are pruned.
- **Landed in #12055 (2026-11-27), unqualified:** the Codex Linux stack (`work/orchestrator-parallel-compose-20261126` at `de58e1997d6`). A resumed Codex session must restart from `origin/release/1.0.0`; the lane branches are superseded. The PR also carries:
  - the V4 node-budget fix;
  - the `remote_pane_view_v1` 35-byte oracle;
  - enrolled-host system specs that now report `pending("BLOCKED: ...")` (exit 6);
  - the SSH loopback verdicts;
  - a fix so the smux V6 owner releases `agent_pane_target` on a detach or cancel of the same run (the review's P1).
- **`primitive_api` ratchet:**
  - Nine internal-only names are no longer `pub`: `linux_agent_admission_v1`, `linux_agent_prepared_v1`, `linux_agent_execute_wire_v1`, `LinuxAgentAdmissionFactsV1` and `dispatch_service_status_v3`, among others.
  - Struct-level `@allow(primitive_api)` on `ServerSshTurnV1` and `OrchestratorValidationReplyV1` also covers their older fields, so a primitive field added later to either struct is not ratcheted.
  - `linux_agent_prepare_wire_v1` and `linux_agent_admitted_invocation_v1` stay `pub` but take values only the now-private entry points produce. Either re-expose the chain for a real consumer or make them private as well.
- **Each run leaks one smux session:** `remote_pane_target_v6` creates an `agent-pane-<digest>` smux session per run, and nothing kills it on detach or cancel. The owner should decide whether it is released with the run.
- **Installer acceptance SSpec:** Codex's uncommitted work from `/tmp/simple-orch-install-acceptance-20261126` (a corrupted-signature refusal plus a genuine install retry) landed together with this handoff. Its unset-fixture path is `pending("BLOCKED: ...")`. It needs `SIMPLE_LINUX_SERVICE_INSTALL_FIXTURE_PARENT`.
- **Ran locally:**
  - Podman session smoke: 5/5, with the entrypoint fixture image.
  - caret-serve/caret-client loopback: status, crashed, cleanup preview and shutdown.
  - Controller journal intent, cancel and foreign-controller refusal.
  - SSH loopback (user sshd on 127.0.0.1:2299): key auth and host-key pinning hold. The round trip is BLOCKED because the seed interpreter lacks `rt_stdin_read`/`rt_stdout_write`, so it needs a compiled `simple-orchestrator` peer.
- **Review P2 items left open:**
  - `agent_run_admission_v1` and `controller_agent_pane_bind_target_v4` have no consumer outside their specs.
  - The remote pane target, turn and dispatch paths are asserted by source-text `index_of` only, so they need state-machine unit specs.
  - Provision reports `installed: false` when the install published but cleanup failed. It still fails closed, and a retry reports `Existing`.
- **Uncapped strict lists** (the owner decides a cap or budget): `remote_run_author_v1` (`expectedTests` + `toolchainInputs` exceed about 227), `storage_view_v1` meta volumes, the `cs_container_lifecycle_v1` host-worktree argv, `caret_session_protocol_v1` crashed records (170 or more), and `wire_envelope_v1` (budget equals the encoder cap, but whether they count the same is unverified).
- **Root alone does not unblock the Linux host rows (checked 2026-11-27).** On the Rust seed interpreter, `linux_machine_policy_open_v1()` fails with `unknown extern function: gettid` before it reads `/etc/simple/container`. Installing the root-owned profiles would not change that, so the host was not modified. These rows need a native binary from a qualified self-hosted compiler, run in a dedicated guest per `linux_fixture_preflight.md`.
- **Blocked rows. Each needs its owner, a prerequisite and the exact resume command:**

| Row | Owner | Prerequisite | Resume |
| --- | --- | --- | --- |
| Native runner qualification | Bootstrap owner | Source-matched self-hosted CLI deployed. Stage-2 verification of `06ba866385d5`: `compiler_cli_build` TIMEOUT (21603 s), `test_runner_build` FAIL at library-unit packaging, still failing on `3dd00937c329`, which contains the `9acdac6f849` workaround; the CLI build there failed with `FILE-WORKER-E-CLOSURE-INCOMPLETE` (`doc/08_tracking/bug/stage2_test_runner_libunit_project_name_missing_2026-11-27.md`) | `sh scripts/bootstrap/bootstrap-from-scratch.sh`, then `sh scripts/check/run-orchestrator-native-qualification.shs bin/simple` (runs every listed spec, the SSH round trip and the guest wrapper; verdicts in `build/orch-native-qual/last-run.txt`) |
| Enrolled Linux Host (provision, startup, V6 attach, installer) | Linux host operator (root) + bootstrap owner | `/etc/simple/container` profiles, a systemd unit with `Delegate=yes`, protected key and credential stores, the six `SIMPLE_LINUX_PROVISION_ACCEPTANCE_*` variables, `SIMPLE_LINUX_ATTACH_V6_READY`, `SIMPLE_LINUX_SERVICE_INSTALL_FIXTURE_PARENT`, per `continuation_20261116/verify_queue/linux_fixture_preflight.md` | `sh scripts/check/run-orchestrator-native-qualification.shs --only cited --no-guest <self-hosted simple>` runs these three with the other cited specs and reports their unset-fixture state as `BLOCKED`. With the fixture exported, the same command gives the real verdicts. The dedicated guest run is `sh scripts/check/check-linux-orchestrator-host-qemu.shs --run-specs <bin>`, which the runner calls last when that script exists |
| Caret SSH gateway / real remote host | Orchestrator verification | A compiled `simple-orchestrator` peer and the `SIMPLE_CARET_SSH_ACCEPTANCE_*` fixture | `sh scripts/check/run-orchestrator-native-qualification.shs --only ssh --no-guest <self-hosted simple>` (builds the peer, starts and stops the user sshd on 127.0.0.1:2299, generates the `SIMPLE_CARET_SSH_ACCEPTANCE_*` fixture). Add `--peer <compiled simple-orchestrator>` to reuse a peer. A real remote host still needs an operator-supplied fixture and `bin/simple test` on the spec |
| Shared-API Linux Podman route (workspace, limits, exec/TTY, cleanup) | Container owner (root) | Installed machine policy under `/etc/simple/container` and `/var/lib/simple/container`; no live spec exists yet (`simple_container_api_v2_spec` and `oci_execution_options_effects_spec` cover only argv and refusals) | Author a live spec through `SimpleContainerApiV2` once the policy is installed |

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

## Linux acceptance order

The Podman session smoke and signed Host startup can prepare independently.
The inspected Linux host reports Podman 4.9.3. Rootless runtime usability,
delegation and the required local images still need verification on the
designated test host.

| Run | Prerequisites | Evidence |
| --- | --- | --- |
| Signed contract and helper-expiry specs | Admitted LLVM AOT runner and a private journal fixture for the helper spec | Run first as soon as the runner is available. Capture exact-head receipts for the signature, association, currentness and reservation tests. |
| Podman session smoke | Qualified self-hosted runtime, usable rootless Podman, local `busybox:1.36`, and the documented local entrypoint fixture image | Set `SIMPLE_PODMAN_SMOKE=1` and `SIMPLE_PODMAN_ENTRYPOINT_IMAGE` as described in the [smoke manual](../../06_spec/03_system/app/container/feature/podman_session_live_spec.md). Record command override, output, nonzero exit, timeout and cleanup with the opt-in active. Then qualify workspace-backed interactive execution through the shared provider. |
| Signed provisioning and startup | Admitted runner, protected machine policy, approved systemd and Podman units, and six operator-provided `SIMPLE_LINUX_PROVISION_ACCEPTANCE_*` settings | Run the pinned startup spec from PR #11928. Retain issuance and exact-retry receipts, the startup evidence and any outstanding cleanup. |

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

## Update 2026-11-27 (late)

- **#12122** (`str_slice` byte offsets) and **#12126** (planning braced qualified re-exports) landed.
  The release-head bootstrap `967f9178950e` no longer hits `FILE-WORKER-E-CLOSURE-INCOMPLETE`.
- **New blocker:** `compiler_cli_build` aborted with `rss-cap-exceeded` (60 GiB). Record:
  `doc/08_tracking/bug/stage2_cli_build_rss_cap_leak_check_closure_2026-11-27.md`.
  Resume with `BOOTSTRAP_VERIFY_MODULE_WORKERS=1`. The `test_runner_build` row (the #12122 fix) is still unexercised.

## Update 2026-11-27 (native qualification prep)

- **Runner:** `sh scripts/check/run-orchestrator-native-qualification.shs <self-hosted simple>`
  runs the 134 `cited` and `inventory` specs of
  `scripts/check/orchestrator_native_qualification_specs.txt` one at a time, then the SSH
  round trip (builds or reuses the peer, generates keys and the `SIMPLE_CARET_SSH_ACCEPTANCE_*`
  fixture, submits one intent, starts and stops a user sshd on 127.0.0.1:2299), then
  `scripts/check/check-linux-orchestrator-host-qemu.shs --run-specs <bin>` when present.
  Verdicts go to `build/orch-native-qual/last-run.txt`. Exit 1 on any FAIL, 2 on a script
  error; BLOCKED and NOT_RUN are counted separately and exit 0. `--selftest` uses a fake binary.
- **Stage-2 peer build: NOT BUILT.** Compiler:
  `build/bootstrap/pinned-src/pinned-967f9178950e/.simple/storage/build/bootstrap/stage2/aarch64-unknown-linux-gnu/simple`.
  Command: `SIMPLE_BOOTSTRAP=1 SIMPLE_CACHE_SCOPE=orchpeer-20261127 systemd-run --user --scope -q -p MemoryMax=30G timeout 14400 <stage2> native-build src/app/orchestrator/main.spl --threads 4 -o <out>`.
  - First error: `cold HIR receipt capture failed: cold-hir-abi-unresolved:unresolved-inference:0:0:declaration=constant:PURE_CONTAINER_BACKEND_V1`
    in `src/lib/common/contracts/container/pure_backend_v1.spl`. Worked around by stating `: text`
    on the two alias constants (bug `p3_cold_hir_unresolved_public_interfaces_2026-10-05`).
    The failed build did not exit: it logged `phase 3 FAILED` three times and was still
    spawning workers 36 minutes in.
  - After the workaround the build compiles cleanly but too slowly. The pool estimates
    43.5 GB per HIR worker against the 30 GB cap and degrades to one serial worker:
    21 objects in 30 minutes, about 75 s per unit, so roughly 20 h for the 976 modules.
  - More parallelism under 30 GB is OOM-killed by the cgroup (rc=143, no compiler message):
    8 or 6 parse shards, and 4 shards with `SIMPLE_HIR_SHARD_WORKER_KB=6000000`.
  - Resume on a free host: `ORCH_QUAL_MEM_MAX=64G sh scripts/check/run-orchestrator-native-qualification.shs --only ssh --no-guest <self-hosted simple>`.
    The parallel path above 30 GB is unverified.
  - Build 3 also logged `[parser_error] std/nogc_async_mut/container/pure_adapter_v1.spl line 80:9`
    and `108:9` (non-fatal there). Check them when a peer links.
- **SSH round trip: still BLOCKED on the compiled peer.** The fixture and transport were
  re-checked with the seed as both runner and peer (diagnostic only):
  `SPEC FILE VERDICT: test/03_system/app/orchestrator/feature/caret_configured_ssh_gateway_spec.spl outcome=ERROR declared>=1 executed=1 passed=0 failed=1 skipped=0 blocked=0 dropped=0`,
  with one peer invocation of `gateway-stdio-v1` over SSH. This is the known
  `rt_stdin_read`/`rt_stdout_write` gap, not a native result.
- **Seed diagnostic of the `cited` group** (`--only cited --no-guest`, Rust seed, not qualification):
  3 PASS (`oci_execution_options_effects_spec` 11/11, `host_identity_v1_spec` 27/27,
  `server_ssh_v1_spec` 14/14), 2 BLOCKED (`host_linux_provision_startup_v3_spec`,
  `linux_agent_attachment_v6_spec`), 2 FAIL:
  - `linux_service_native_identity_v3_spec` 3 failed: `unknown extern function: gettid` (seed limitation).
  - `simple_container_api_v2_spec` 2 failed: it reads `build/simple-container-api/linux-case.sdn`
    and `windows-case.sdn`, which nothing in the repo creates, and unwraps the error instead of
    reporting `pending("BLOCKED: ...")`. Until the fixture exists or the spec is changed, the
    runner exits 1 on this host.
