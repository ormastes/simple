# Distributed execution: full acceptance inventory and verification handoff

Status: **AWAITING_VERIFICATION**. Snapshot: 2026-11-07.
Owner: Astra system acceptance; root owns final integration and execution grants.
This is the persistent central verification handoff.
The latest user instruction is to update full tests/docs, await verification, and
use at most **five CPU cores total**. No build or runtime test is launched here.

Source landing, authored scenarios, diagnostic execution and admitted acceptance
are distinct. The distributed-execution objective is incomplete. Missing complete
paths below are concrete BLOCKED prerequisites, not placeholder passing tests.

Reuse the controller lane's merged verification inventory rather than duplicating
its requirement definitions: PR #7587, merge
`8731af00a0fc9b264e5e38ca4034e27f6b04a69c`,
`doc/03_plan/sys_test/orchestrator_verification_wait_20261107.md`, and
`.spipe/simple_orchestrator/verification_wait_20261107.sdn`. It records 50 local
authored cases plus the six public CLI cases, not 56 executed cases.

## Landed modern public CLI acceptance

Controller metadata source: PR #7578, merge
`a6dca22ee32da27ff9e45a67ba86ae3ef587074e`.
Caret client source: PR #7554, merge
`26fa1f0baded05c8e9771bb1b323f720105c6315`.
Modern acceptance source: PR #7582, reviewed head
`2fdcf3338d8da9398872d6076d518a5b5b7a6a0f`, merge
`490935a4a7cd8347ef2fe1d5b5c6afe0e48d6ba2`.

- Executable: `test/03_system/app/orchestrator/feature/caret_controller_cli_acceptance_spec.spl`.
- Shared real-subprocess helper: `test/fixtures/orchestrator_acceptance/caret_controller_cli.spl`.
- Authored manual: `doc/06_spec/03_system/app/orchestrator/feature/caret_controller_cli_acceptance_spec.md`.
- Scope/traceability: `doc/03_plan/sys_test/caret_controller_cli_acceptance.md`.

Six scenarios are AUTHORED_UNRUN: fresh-process submit/inspect; identical replay;
changed source under the same UID; wrong-controller inspection; relative
executable refusal; extra-argument refusal. Each uses actual public subprocesses.
The independent oracle checks the committed V2 operation, payload/controller/UID
association, exact retained source and WAL CURRENT; it does not use the product
decoder as its own expected-result generator. Both binary hashes are observed
around invocation. The journal observation lease is a plain 64-hex nonce and is
closed before assertions on the snapshot. Manual/source review and static/push
gates passed; native execution and docgen did not run.

This metadata subset must still report `executionAuthorized=false`, unbound
assignment and unobserved runtime. It closes no host/container/mux/RUN execution
requirement. The full-system helper names and step labels remain those frozen in
the full-system interface below; metadata helpers deliberately have a separate scope.

## Frozen full-system test interface

The shared test helper names are `orchestrator_acceptance_fixture`,
`orchestrator_acceptance_submit`, `orchestrator_acceptance_observe`,
`orchestrator_acceptance_cleanup`, `expect_orchestrator_acceptance_receipt` and
`expect_orchestrator_provider_effect`. They are proposed test interfaces, not
implemented production APIs; signatures must use the actual landed owner types.
No placeholder success body may be introduced.

The exact full-system manual `step()` labels are:

1. `Open isolated controller and authenticated host owners`
2. `Submit one pinned workload through the public client`
3. `Observe the primary process through the bound terminal`
4. `Verify runtime identity and durable ownership independently`
5. `Replay the same request without a second execution`
6. `Reject changed or stale authority without another effect`
7. `Recover an uncertain reply without repeating the workload`
8. `Destroy the exact runtime object before releasing capacity`
9. `Preserve unrelated workloads and retained evidence`

Use these labels only when their real behavior is exercised. Metadata-only cases
use their own narrower labels. A future primary execution scenario must observe
one fresh nonce from the real workload through the actual sole terminal reader,
independently inspect its exact native identity, verify durable grant/assignment
correlation, prove replay has one effect, and establish native absence before
capacity release. An output-only mechanism test cannot close the whole lifecycle.

## Current lane inventory

Source states below are reported by the responsible lane owners at this snapshot.
An uncommitted worktree or an isolated commit is not a merged product. All listed
SSpec scenarios remain unexecuted under an admitted producer unless explicitly
stated otherwise. Manuals mirror `test/...` at `doc/06_spec/...`, replacing `.spl`
with `.md`; authored mirrors are not generated execution evidence.

### Daemon and operation authority — DAE-01..05

Source landed: #7533 `5854838c6124cfa9deb6c0d985814dd9db8bfe0e` (shared dispatch,
exact lock); #7562 `83ff7eff2ab` (authority foundation); #7564 `40a8955416c`
(owned poll); #7560 `043481d26a9` (interpolation producer repair).

Executable inventory:

- `test/02_integration/lib/daemon_sdk/response_ack_spec.spl`
- `test/02_integration/lib/daemon_sdk/spool_admission_spec.spl`
- `test/02_integration/lib/daemon_sdk/spool_byte_limit_spec.spl`
- `test/02_integration/lib/daemon_sdk/operation_dispatch_v2_spec.spl`
- `test/01_unit/lib/daemon_sdk/daemon_sdk_exact_lock_owner_spec.spl`
- `test/01_unit/lib/daemon_sdk/daemon_sdk_owned_poll_v1_spec.spl`
- `test/01_unit/lib/daemon_sdk/distributed_grant_verification_v2_spec.spl`
- `test/01_unit/lib/daemon_sdk/distributed_authority_snapshot_v2_spec.spl`
- Native diagnostics: `test/fixtures/native_daemon_exact_lock_owner/main.spl`,
  `test/fixtures/native_daemon_owned_poll_v1/main.spl`, and shared cases under
  `test/fixtures/daemon_sdk/`.

Evidence scope: one lock-only unadmitted diagnostic passed; byte-limit diagnostic
passed three real-file cases. Earlier publication diagnostics had six successes
and three failures, including an observed acknowledgement path-hash disagreement.
Owned-poll builds failed before linking on the older fill-span dependency; no
owned-poll runtime pass exists. The changed producer has not qualified these cases.
Generation-bearing piped-reference ownership is draft #7603, final head
`c65e96f575708dfb2c6948779c72c7d4a2a289de`, exact Astra review `5810534096`.
Its ten files/two commits remain AWAITING_VERIFICATION. Exact paths are
`src/runtime/test/piped_process_ref_v1_selfcheck.c`,
`test/fixtures/piped_process_ref_v1.spl`,
`test/01_unit/lib/io/piped_process_ref_v1_spec.spl`, and
`test/fixtures/native_piped_process_ref_v1/main.spl`; design/manual are
`doc/05_design/piped_process_ref_v1.md` and its I/O spec mirror. They are NOT_RUN.
This is registry-generation safety, not a kernel PGID-incarnation supervisor.
The final source has three shared SSpec/native-Simple scenarios and a native C
actual-registry selfcheck; all are NOT_RUN. Source review confirms the behavioral
test entrypoints exist; no executed fixture or live provider/mux qualification is
claimed. Run the SDK and Caret fixtures in separate host processes: the SDK keeps
one registry slot and the Caret mechanism scenario keeps two of sixteen.
The current POSIX design explicitly returns `process_close_unsupported` (native
-3) for a valid generation ref, without signals, FD close or slot release; stale
-2 is distinct. Its bounded 16-slot registry retains ownership. Smux must retain
pane/session/window and refuse removal. Successful POSIX teardown and duplicate-
after-release testing are BLOCKED_CAPABILITY until an exact group owner exists.
Windows HANDLE/job close has a separate authored/unrun qualification lane.
POSIX generation-ref liveness is also explicitly unsupported:
`process_liveness_unsupported`, native -3, without waitpid or signals. Another
canonical reaper plus PID reuse prevents registry generation from proving kernel
child identity. Generation-checked read/write/EOF remain separate operations;
EOF is not process exit and cannot justify teardown or capacity release.

### Host authority and execution — HOST-01..03

Source landed: #7551 `21b6030` (capacity/replay owner); #7572 `12905ea`
(protected local-authority policy). Enrollment/claim source is draft #7594,
reviewed head `a2b3c8c1ddbc0e6bacf6dd1379d38dca99bf147f`,
AWAITING_VERIFICATION: six credential and five real-crypto/filesystem claim cases
are authored, all NOT_RUN. Its scoped inventory is
`doc/03_plan/sys_test/host_enrollment.md`; structured status is
`doc/05_design/host_enrollment_verification.sdn`. No host-service execution is
claimed by this draft.

System spec prefix: `test/03_system/app/orchestrator/feature/`:
`host_prepare_replay_spec.spl`, `host_config_source_spec.spl`,
`host_execute_request_spec.spl`, `host_enrollment_spec.spl`, and
`host_enrollment_claim_spec.spl`, plus `local_authority_policy_spec.spl`.
Corresponding real-owner native probes live at
`test/fixtures/orchestration/*_native_probe.spl`.
The signed claim fixture is
`test/fixtures/orchestration/host_enrollment_claim_fixture_v1.spl`.

One old unadmitted host diagnostic timed out after 240 seconds with no executable.
Host execute-request shape tests using shape-valid zero signatures do not prove
authorization. Signed protected-filesystem tests remain authored/unrun.
Public host-local-init/host-prepare/host-execute/host-inspect command composition,
native observation wiring, retained execution observations and provider recovery
are not implemented/wired at this snapshot.
The new `host_enrollment_claim_spec.spl` calls the actual signed filesystem claim
consumer and checks retained config/policy/credential files and permissions. Its
adjacent cases include forged/expired signatures, expiry immediately before
publication, existing pending/unknown claims and escaping configuration. These
are behavioral authored cases; their presence does not prove runtime execution.

### Controller planning and public metadata — ORCH-01..03, CFG-01/02, OPS-01

Source foundations include merged resource/profile and prerequisite work (#7544,
#7568); #7578 supplies the real metadata main/commands. System spec prefix is
`test/03_system/app/orchestrator/feature/`:
`resource_profile_foundation_spec.spl`, `placement_spec.spl`,
`controller_workload_fence_spec.spl`, `resource_set_ci_prefix_spec.spl`,
`local_controller_process_spec.spl`, and the six-case public Caret acceptance above.

The resource-profile probe passed only as an unadmitted native diagnostic.
The packet diagnostic failed on the older fill-span producer dependency; no
packet binary/runtime pass exists. All admitted SSpec and metadata subprocess
execution remain NOT_RUN.

`dispatch <root> <controller> <uid> <file>` and
`inspect-execution <root> <controller> <uid>` are agreed planned interfaces,
NOT implemented commands. A future local in-process host-core composition uses
independent journals; it cannot be described as remote transport qualification.
Immutable administrative route/epoch/policy configuration and actual host/provider
observations are required before authoring a positive dispatch execution case.

### Canonical OCI provider and CI — CTR-01..03

Source landed: binding #7565, source
`6c1e9968f374162ad0d943c2f12cc1ccb50cb070`, merge `cb9a4908`;
command mapping #7574, source `a314ee0fe824c8d73b41d5ff08aaa93b3d7ede1e`,
merge `1e6c8d5d`.
Trusted engine-policy source is draft #7589, exact reviewed head
`f40583ec5d0b1fbb343fc6db6fd2b2dcdc6558c4`, AWAITING_VERIFICATION.
Its 11 authored cases are
`test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_engine_policy_spec.spl`
with corresponding authored manual; trust limits and pending matrix are in
`doc/05_design/oci_trusted_engine_policy_admission.md`.

Concrete specs:

- `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_request_binding_spec.spl`
- `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_request_codec_spec.spl`
- `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_runtime_v1_spec.spl`
- `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_entrypoint_override_spec.spl`
- `test/01_unit/lib/common/contracts/container/oci_command_parts_spec.spl`
- `test/02_integration/app/ci/container_backend_selection_spec.spl`
- `test/02_integration/app/ci/container_command_mapping_spec.spl`
- Real-journal fixture `test/fixtures/orchestration/oci_binding_admission_fixture.spl`
  and native entry `oci_binding_admission_native_probe.spl`.

These are source/contract/journal checks, not live Podman qualification.
The binding fixture invokes production provider prepare/create/recover/inspect/
stop/destroy against retained journals with scripted engine replies. It checks
changed payload/operation refusal without another executor call and legacy cleanup
behavior. CI mapping checks use the real mapper/builder for override, default and
args-only cases; they do not execute an image ENTRYPOINT.
The new policy cases exercise production policy/observation parsing and provider
admission with scripted engine info/replies; changed executable identity refuses
before a scripted effect is consumed. Real installed dynamic-Podman observation
and host comparison with signed enrollment after restart remain unexecuted.
`simple_container_cross_host_spec.spl` under the container system feature tree is
explicitly contract/preflight scope. Engine-policy and terminal-session owners are
WIP. Required provider inputs are an approved absolute installed Podman binary,
actual rootless identity/subids/cgroups, approved graph/run roots/driver/options,
and a known locally available digest-pinned image. Do not silently pull an image,
escalate privileges or substitute Docker/host execution during acceptance.

### Caret and CoreMux — CARET-01..02, MUX-01..02

The client #7554 and metadata acceptance #7582 are landed. Pure checked-client
coverage is `test/03_system/app/llm_caret/feature/orchestrator_client_spec.spl`.
Current MUX source is draft #7596, final head
`8f7e8f854585f7e6d9aa999f40229a1ae3323b1b`, dependent on the final pipe head
`c65e96f575708dfb2c6948779c72c7d4a2a289de`. It has
`test/03_system/app/llm_caret/feature/smux_runtime_binding_capabilities_spec.spl`
and matching manual; the draft is not a landed live runtime binding.
`test/01_unit/os/apps/smux/runtime_terminal_ref_spec.spl` exercises production pane
state/clone/input/rollback logic with synthetic refs, including generation changes,
read-only input/resize refusal and stale rollback. That is pure state behavior.
The final actual bounded-helper -> adoption -> pane_poll -> fresh bytes/EOF
consumer scenario is
`test/03_system/app/llm_caret/feature/smux_runtime_terminal_transport_spec.spl`,
with its authored mirrored manual. Final source review covers five route cases,
five pure ref-state cases and this one real-helper scenario; all eleven remain
AUTHORED_UNRUN. Exact registry membership validation is not liveness proof.
Its agreed POSIX scope is now positive output drain plus expected close refusal,
exact ref/pane retention and an unaffected unrelated finite helper, in an isolated
process using at most two retained slots. It must not assert successful teardown
or slot reuse where the provider explicitly reports unsupported cleanup.
Existing `session_runtime_binding`, `session_runtime_lease`,
`session_binding_store`, and `smux_terminal_pipe` specs under the orchestrator
feature directory prove contracts/storage only, not an actual relay.

The first agreed attach scope is OUTPUT ONLY: generation-bearing piped reference,
`--no-stdin --sig-proxy=false`, input/geometry/interactive capabilities false.
Spawn/adoption proves helper ownership/opening only. A positive gate requires a
fresh workload nonce delivered by the sole real `pane_poll` reader plus independent
engine inspection. A ref, PID, empty frame or capabilities response cannot pass.
Host-retained resolver, provider TerminalSession, configured binding journal and
the Caret runtime consumer remain required. Input/resize/TTY support is a separate
blocked acceptance obligation, not implied by output attachment.

### Build/test runner — RUN-01..02

Existing `test/02_integration/app/buildrunner/distributed_submission_spec.spl`
remains relevant. No inventoried scenario establishes the complete public
controller -> host -> provider -> parent-verified result/output path.
Preserve TaskRunnerV1 and parent-authoritative acceptance; do not replace the
missing adapter with a direct local executor or trust a remote success string.

## Toolchain and transport prerequisites

- SDN source #7542 merged `d038889d84523ca5c08de4981b60270ba7d5fffd`, reviewed
  head `790586bac1d0`: `test/01_unit/compiler/frontend/flat_bridge_string_scan_spec.spl`,
  `test/01_unit/compiler/interpreter/pure_simple_frontend_interpolation_promotion_spec.spl`,
  `test/01_unit/lib/common/sdn/sdn_inline_collection_delimiters_spec.spl`, and
  `test/fixtures/compiler/sdn_nested_literal_integrity.spl`. Source correctness is
  not evidence that a usable producer now preserves nested quantities.
  The missing authored mirrors and flat-bridge status refresh landed via #7595,
  merge `4d106c0a0d41e25b6bfd4d93c835a9d42ec164d8`, reviewed head
  `4d53190983eea0c1957a8830753b97b5a3b21975`. Their exact paths are
  `doc/06_spec/01_unit/compiler/interpreter/pure_simple_frontend_interpolation_promotion_spec.md`,
  `doc/06_spec/01_unit/lib/common/sdn/sdn_inline_collection_delimiters_spec.md`, and
  `doc/06_spec/01_unit/compiler/frontend/flat_bridge_string_scan_spec.md`.
  The authored-document gap is resolved; actual execution and generated-manual
  validation remain pending. Their frozen source hashes are retained explicitly.
- TCP Copy/Move source #7530 merged
  `0d9369779c9064645edb4e52160fdbf92a0fcb9d`; later store conversion work requires
  its owner's exact reviewed source handoff. Known checks include
  `test/01_unit/compiler/backend/u8_copy_widening_spec.spl` and
  `test/fixtures/compiler/i8_checked_window_native_probe.spl`. The latter is a
  SIGNED control checking -128/-1/0/127; it is not the unsigned high-bit reproducer.
  A separately identified unsigned checked-window spill/reload fixture and actual
  framed TCP consumer must run with the changed producer. Direct-call or signed-
  control success cannot substitute for those gates.
- Process-capture #7337 landed at
  `82eeb7004fd30993f5936cbc7cd28d714e549827`, exact reviewed source
  `59fe725a000ff94963de67929ec5a3f5eb4587b5`, Astra/Sol review `5810507181`.
  Relevant source is the canonical process-capture SFFI owner and
  Rust provider; tests include
  `test/01_unit/lib/nogc_sync_mut/process_capture_owned_result_spec.spl`,
  `test/fixtures/compiler/process_capture_owned_block/main.spl`, and
  `test/fixtures/compiler/process_capture_canonical_owned_block/main.spl`.
  Historical Rust owner tests were diagnostic only; the actual Linux caller
  failed with exit 14 and target linked provider unknown. Six old cycles are
  exhausted. Source landing cannot erase that failure or prove Windows nativeall
  linking. The source-matched linked-provider identity/capture gate remains open.
  The authored five-case manual is
  `doc/06_spec/01_unit/lib/nogc_sync_mut/process_capture_owned_result_spec.md`.
  The spec invokes real process capture and checks stdout/stderr/status, with
  null/empty/invalid payload prevention; none of those source assertions is an
  admitted executed verdict.
  Diagnostic follow-up #7547 remains a separate unexecuted draft; its production
  prerequisite is now landed, but this does not authorize another exhausted retry.

Fresh cold fill-span evidence is retained at
`/home/yoon/dev/simple-fill-span-transition-probe-20261107/build/fill-span-extern-cold-1/result.sdn`.
Source `5149a588e1261794d77d1c416a01628253686759`; producer SHA-256
`bc9d676a0bb185378b72035f99de892c5af3b0169e6207559f9e385d3a4cb106`;
emitted binary `eeaff06626d329423c396561f0995f6494e57a6ef16e07104cb2a25f03227089`.
Build/run exited 0, with one cold module and no reused module or production
overlay. All 57 source assertion sites completed without assertion failure;
instrumented assertion count was unavailable and modern SSpec was not executed.
Actual AArch64 primitive/barrier code was reviewed. LLVM IR was requested but not
retained, representation warnings remain, and linker identity was recorded after
the build rather than prebound. This is useful diagnostic PASS, **not admission**.

The next producer chain is planned only: bridge B using the explicitly recorded
overlay -> B real Hello -> pristine current-source C -> C real Hello -> source-
matched full CLI/test runner -> actual SSpec/docgen. The SDN owner's adjacent
`bridge-handoff.sdn` and `verification-inventory.sdn` are finalized and source-
reviewed by Astra and Sol. They bind successor source
`b7b3845d2e0a6e0811638965be9b2ca902a9791d`, the isolated four-call secure-memory
overlay for B only, pristine C, and the Linux 14-symbol driver projection from
the existing three runtime source owners. Actual cc and all tool/runtime/header
inputs must be prebound; no new C implementation or old receipt restamping is
permitted. Full CLI entry is `src/app/cli/_CliMain/main_and_help.spl`; standalone
runner entry is `src/app/test_runner_new/main.spl`. The receipt explicitly grants
zero launch attempts now. No bridge/provider build is authorized by this inventory.

## Concrete full-system case backlog

These are required acceptance cases, not executable placeholders. Author the
actual modern spec only when the named production consumer exists. Each case
must use real assertions and independent observations; missing dependencies are
BLOCKED and never a passing skip.

| Case / requirement | Actual action and independent oracle | Required production prerequisite |
| --- | --- | --- |
| AT-DAE-PUBLISH / DAE-01 | Lose publication after real effect; retained operation remains accountable and retry does not repeat effect | Consumed service publication/recovery boundary and source-matched executable |
| AT-DAE-OWNER / DAE-02 | Competing owner/reopen cannot release another generation's lock or execute its work | Integrated exact owner lifecycle and process-recovery consumer |
| AT-DAE-BOUND / DAE-04/05 | Saturate bounded dispatch while control/health remains responsive; interrupted durable transitions reconcile | Actual event loop/scheduler, authoritative clock and durable transition receipts |
| AT-HOST-ENROLL / HOST-01 | Install signed approved host claim; reject wrong native identity, boot/provider/policy or protected-root ownership | Real administrative provisioning and native observation consumer |
| AT-HOST-FENCE / HOST-02 | Reject stale grant/epoch and exhausted capacity before any native effect | Actual signed prepare/execute consumer and independent runtime inventory |
| AT-HOST-RECOVER / HOST-03 | Reopen after uncertain execution; retain charge until exact native absence; no relaunch | Durable execution observation store and provider reconciliation |
| AT-ORCH-DISPATCH / ORCH-01/02 | Submit one pinned workload through actual dispatch, observe fenced placement and correlated host/native IDs | Implemented dispatch plus route/epoch/policy configuration and host provider composition |
| AT-ORCH-POLICY / ORCH-03 | Competing scarce-resource jobs obey approved placement/fairness policy with independently observed allocations | Implemented policy consumer and known target-policy assertions |
| AT-CTR-RUN / CTR-01 | Actual digest-pinned rootless Podman primary process emits fresh nonce; engine inspect matches exact native ID | Approved installed provider, local image, rootless host capability and consumed request binding |
| AT-CTR-LIMIT / CTR-01 | Requested CPU/memory/PID/read-only/network policy is observed at actual runtime/cgroup boundary | Real host enforcement and observable limits; argv alone is insufficient |
| AT-CTR-CLEAN / CTR-02 | Exact stop/destroy preserves unrelated sentinel and proves native absence before ledger release | Consumed exact cleanup/recovery owner |
| AT-CTR-WINDOWS / CTR-03 | Run/inspect/cleanup on actual supported Windows process-container provider | Separately configured Windows host/provider/toolchain; Linux success cannot substitute |
| AT-MUX-OUTPUT / MUX-01 | Fresh nonce arrives through actual sole pane reader and matches independently inspected container | Host resolver + provider output TerminalSession + journal + Caret/CoreMux consumer |
| AT-MUX-AUTHORITY / MUX-02 | Observer/expired lease cannot input/resize/stop or gain host control | Actual binding/control dispatch and owner-issued/revoked lease |
| AT-MUX-INTERACTIVE / MUX-01/02 | Authorized stdin and resize affect the actual primary PTY without crossing identities | Separate admitted interactive creation, stdin/TTY/geometry capabilities and routing |
| AT-CARET-CREATE / CARET-01/02 | Public IaC session-create reaches actual approved provider invocation and retained workspace | Consumed client->controller execution path plus explicit provider/version capability |
| AT-RUN-ACCEPT / RUN-01/02 | Parent accepts real remote semantic/output evidence tied to exact request/assignment; reject forged or stale output | Shared RUN adapter and existing parent-authoritative validation consumer |
| AT-END-TO-END / combined | Public submit -> authenticated host -> real primary process -> actual smux nonce; identical replay yields one effect; exact cleanup then releases capacity | All preceding positive-path owners, real artifacts and independently observed native state |

Further FreeBSD/Apple/Kubernetes extension cases remain separately BLOCKED by
their specific product/provider/platform handoffs. This Linux first slice does
not advertise cross-platform qualification.

## Exact command templates for the next verification window

These are templates, NOT execution receipts. Replace the `/absolute/...` paths
with root-validated immutable source/producer/runtime artifacts before use.
No source `--list` result is a binary-owned test count. Inspect the emitted test
binary's supported listing interface rather than inventing flags.

Root must first bind one immutable reviewed candidate containing the needed
published draft deltas: pipe #7603 `c65e96f575708dfb2c6948779c72c7d4a2a289de`,
Caret #7596 `8f7e8f854585f7e6d9aa999f40229a1ae3323b1b`, host #7594
`a2b3c8c1ddbc0e6bacf6dd1379d38dca99bf147f`, and engine policy #7589
`f40583ec5d0b1fbb343fc6db6fd2b2dcdc6558c4`, in dependency order. These are draft
source inputs, not merge or execution receipts. Validate their exact owned deltas
and resulting tree identity; do not copy arbitrary dirty worktrees or assume
release already contains their new executable specs. This source assembly does
not implement the explicitly absent host dispatch/provider binder.

Source entrypoints to compile with the admitted producer:

```text
src/app/orchestrator/main.spl
src/app/llm_caret/main.spl
```

Native product build shape, with private writable caches/TMPDIR and the producer's
receipt-bound runtime selection supplied by root:

```sh
taskset -c 0-4 /absolute/admitted/simple native-build --backend llvm --source src --entry-closure --entry src/app/orchestrator/main.spl --threads 5 --mode one-binary --output /absolute/private-run/simple_orchestrator
taskset -c 0-4 /absolute/admitted/simple native-build --backend llvm --source src --entry-closure --entry src/app/llm_caret/main.spl --threads 5 --mode one-binary --output /absolute/private-run/llm_caret
```

Run builds serially, never as a two-command parallel shell batch. Runtime bundle
and target flags must match the admitted producer receipt; this template does
not authorize guessing them or using a bootstrap-only runtime as admission.

Metadata system acceptance through the existing full CLI:

```sh
taskset -c 0-4 env SIMPLE_BINARY=/absolute/admitted/simple SIMPLE_BIN=/absolute/admitted/simple SIMPLE_NATIVE_BUILD_THREADS=5 SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_NO_BOOTSTRAP_DELEGATE=1 SIMPLE_CARET_ACCEPTANCE_BINARY=/absolute/private-run/llm_caret SIMPLE_CARET_ACCEPTANCE_SHA256=REPLACE_WITH_EXACT_64_HEX_DIGEST SIMPLE_ORCHESTRATOR_ACCEPTANCE_BINARY=/absolute/private-run/simple_orchestrator SIMPLE_ORCHESTRATOR_ACCEPTANCE_SHA256=REPLACE_WITH_EXACT_64_HEX_DIGEST SIMPLE_ORCHESTRATOR_ACCEPTANCE_ARTIFACT_ROOT=/absolute/private-run/metadata-evidence /absolute/source-matched/simple test test/03_system/app/orchestrator/feature/caret_controller_cli_acceptance_spec.spl --native-backend=llvm --unstable --assert-ran --no-cache --no-db --no-session-daemon --sequential --keep-artifacts --verbose --format text
```

The same native-test invocation, with the positional spec path replaced, applies to each
concrete spec in the lane inventory once its source/providers are integrated.
Use a separate backend run directory for Cranelift. Execute each accepted case
once, retain failed/unexecuted counts, and do not repeat an unchanged green run.
Broader suites must not hide a failed file behind a successful aggregate exit.

After real SSpec execution, generate and review each affected manual:

```sh
taskset -c 0-4 /absolute/source-matched/simple spipe-docgen test/03_system/app/orchestrator/feature/caret_controller_cli_acceptance_spec.spl --output doc/06_spec --no-index
```

Require complete/zero-stub output and review visible steps plus folded executable
against retained case evidence. Until that happens, retain AUTHORED_UNRUN/manual
labels. Required core/lib/MCP/LSP checks and native smokes remain separate gates;
metadata or a toolchain microprobe cannot satisfy them.

Required core/tooling source checks, after the source-matched full CLI is available:

```sh
taskset -c 0-4 /absolute/source-matched/simple check src/compiler
taskset -c 0-4 /absolute/source-matched/simple check src/lib
taskset -c 0-4 /absolute/source-matched/simple check src/app/mcp
taskset -c 0-4 /absolute/source-matched/simple check src/app/simple_lsp_mcp
taskset -c 0-4 env SIMPLE_LIB=src /absolute/source-matched/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter
taskset -c 0-4 sh scripts/check/check-core-runtime-smoke.shs /absolute/source-matched/simple
taskset -c 0-4 env SIMPLE_BINARY=/absolute/source-matched/simple MCP_SERVER=/absolute/private-run/simple_mcp_server LSP_MCP_SERVER=/absolute/private-run/simple_lsp_mcp_server sh scripts/check/check-mcp-native-smoke.shs
```

The repository-required interpreter compatibility check is not native SSpec
execution and must not supply an executed-scenario count. The native MCP smoke
requires independently built, source-matched server artifacts. Use the existing
native-build server entry closures if those artifacts are unavailable; record that
as an additional blocked build dependency rather than silently using old wrappers.
Npm package smoke is conditional on package/publication-flow changes, not inferred
from this documentation-only handoff.

## Five-core aggregate execution schedule

1. **Now: no builds.** Finish exact source/manual review and inventory only.
2. In a later explicitly granted window, root binds one source snapshot and the
   full producer chain. One heavy build runs at a time with <=5 workers,
   `SIMPLE_FILE_WORKERS=1` and `SIMPLE_MIR_FORK_WORKERS=0`, as bound in the
   reviewed producer handoff.
3. All local campaign lanes use the same `taskset -c 0-4` allocation. Five cores
   is the aggregate ceiling, not five per lane. Subprocesses inherit affinity;
   existing external daemons/remote services require their own resource admission.
4. Retain per-stage source/compiler/runtime/provider/link identities, logs,
   hashes, exits, peak RSS, timeout and active-process/affinity observations.
   Independent lightweight checks may overlap only inside the same allocation.
5. Build the source-matched CLI/runner and product binaries before native specs.
   Run native spec processes sequentially, then docgen. Do not launch multiple
   compiler-worker pools from concurrent spec processes.
6. Run full Podman/mux cases only after provider/image/authority/stream consumers
   exist and resource scope is confirmed. Do not assume host task affinity caps
   an already-running container engine or change GitHub-hosted runner settings.
7. Stop at a new blocker with retained evidence. Honor prior six-cycle exhaustion;
   worktree/session changes do not reset it. Source changes or independently
   changed prerequisites must justify any retry.

## Handoff verdict

**AWAITING_VERIFICATION**, not complete and not release-qualified. Modern metadata
acceptance is landed and authored; live full-system cases are concretely blocked.
Producer bridge/pristine/full-CLI, actual SSpec/docgen, canonical provider ABI,
host execution composition, Podman availability, CoreMux output adoption and
parent RUN evidence remain open. Only real future execution can change those
rows to diagnostic or admitted PASS, with the evidence class retained explicitly.

## Subsequent Linux native pipe-registry verification — 2026-11-07

The continued goal run executed the C registry selfcheck from draft #7603 at
`c65e96f575708dfb2c6948779c72c7d4a2a289de`. Its syntax check, compilation and one
native run passed. This supersedes only the earlier NOT_RUN status of that
Linux C selfcheck. The original handoff did not execute runtime tests; the
subsequent evidence is recorded separately below. The three Simple facade
scenarios, Windows behavior, smux consumer and full system remain unverified.
The draft remains AWAITING_VERIFICATION and is not admitted or merged by this
result. No previously passing diagnostic was repeated.

The harness includes the actual `runtime_process.c` owner and links normal
CoreC owners. It exercised real child processes/pipes, exact generation lookup
with deterministic same-PID registry coexistence/replacement, stale operations,
UTF-8 partial writes/tail/EOF, pipe saturation and invalid bounds, input limits,
generation exhaustion and independent legacy-PID compatibility. Forwarding
syscall observers confirmed no wait or signal from unsupported POSIX lifecycle
queries. The harness's test-only retirement/reaping is not a production cleanup
capability, and the deterministic registry case is not an observed kernel PID
reuse race. No branch-coverage measurement was taken.

Both compilation and execution inherited CPU affinity `0-4`. Compilation used
a 120-second timeout and execution a 30-second timeout, each with a five-second
termination grace. Assertions remained enabled (`-O0`, no `NDEBUG`). There were
no runtime/provider stubs or duplicate `runtime_process.o`: the owner is compiled
through the harness include exactly once. Source hashes were checked before and
after compilation; the executable hash was checked before and after execution.

- Build: exit 0, empty compiler log, source unchanged.
- Run: exit 0; `piped process Ref V1 registry/reader boundary: PASS`.
- Executable SHA-256: `c188c0d8dd467462c71f47fedd74324270e0bf6674e5e256458b92f344c441c4`.
- This is a native C boundary result, not an admitted Simple/compiler result.
- POSIX liveness and close remain unsupported; the passing test verifies their
  refusal and retained ownership, not operational process supervision.

The retained local evidence directory is:

`/home/yoon/dev/simple-piped-generation-owner-20261107/build/root-piped-ref-verification-20261107`

It contains `inputs.sdn` (compiler and source/header hashes), `command.txt`,
`build-result.sdn`, `build.log`, `run-result.sdn`, `run.log` and `selfcheck`. The
manifest digests are retained in the central SDN status. These local artifacts
are not claimed to be uploaded CI artifacts; another host must reproduce them
from the pinned draft source. System-header/SDK inputs are not an admitted
toolchain receipt.

The compiler invocation, adapted from the existing native CoreC process checks,
is retained verbatim in `command.txt`. It uses `clang`, the test translation
unit, and these production owners: `runtime_native`, `runtime_legacy_core`,
`runtime_memory`, `runtime_simd_dispatch`, `runtime_simd_utf8`,
`runtime_process_owned`, `runtime_process_tree`, `runtime_memtrack`,
`runtime_fork`, `runtime_timestamp`, and `runtime_thread`; all from the same
draft checkout. Flags preserve the standalone CoreC memory/timestamp ownership
and native array packing contract. No Rust seed or compiler bootstrap was run.

Astra independently checked the source/binary hashes, actual CoreC composition,
active assertions and executable reachability without rerunning the test. The
original child invocation was:

```text
timeout --kill-after=5s 30s /home/yoon/dev/simple-piped-generation-owner-20261107/build/root-piped-ref-verification-20261107/selfcheck
```

It inherited affinity `0-4` from the `taskset -c 0-4 python3 -` parent that
recorded the run. `run-command.sdn` preserves this original invocation after
the review requested it; no rerun was used to produce that record. The exact
wall-clock start timestamp was not captured. Elapsed time is recorded, and this
limitation remains explicit rather than inferring a start time from file dates.
