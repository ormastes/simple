# Local metadata controller CLI

## Actual adopted scope

Base: 2cad1e4edfe on work/orchestrator-controller-cli-20261107. The19-module
metadata source closure supplies compiled main/command/validation/explain/
local_controller/inspection entrypoints, desired/policy/resource-set schemas and
the existing single-writer workload store over distributed-operation V2.
This is callable local metadata functionality for Caret: local-init, submit,
pin-policy, inspect and pending-intent cancel. The local private state root and
its existing marker are the authority boundary. Input schemas and source digests
are not permission to execute work. No controller dispatch or OCI effect is
implemented by these metadata commands. TaskRunner retains parent acceptance.

The source is preserved from /home/yoon/dev/simple unmerged prototypes. Main is
read-only. No historical .spipe state or PASS evidence is copied. CI value decoder
refactoring shares the strict resource parser/envelope and threads source prefixes
through Job/Pipeline errors; focused regression fixtures preserve direct and
nested values, rejection paths and positive original source coordinates.

## Workload store factor

The original prototype has38 declarations. Only the metadata base's28 declarations
are adopted. Provider/placement/invocation/image-specific methods and
ControllerAgentLinuxExecutionV1 remain reviewed staging under
build/orchestrator-controller-cli/src/lib/nogc_sync_mut/orchestration/
workload_store_execution_v1.spl, with unresolved execution dependencies. They are NOT part of this PR and
were never admitted APIs in this branch. No execution extension file is copied.

Base replay retains EVERY original domain: controller_agent_policy_v1,
controller_desired_input_v1, controller_desired_cancel_v1,
controller_assignment_v1 and controller_workload_revision_v1. Pending metadata
recovery, assignment object checks and foreign-operation rejection remain exact.
There is one writer/journal and no alternate metadata namespace. All adopted
base declaration bodies remain identical to original prototype after declaration
visibility normalization. Existing publish/bind_checked helpers become explicitly
trusted internal extension ports; exposing a callable helper grants no authority.

HostConfigV1 is adapted only with decode_host_config(source), which rejects
sources beyond1MiB UTF-8 bytes through common.string_core.str_len, then calls
parse_resource_document and the existing value decoder. Type and value decoder
semantics remain exact. Administrative configuration cannot attest native host
identity, enroll a host or prove available capacity. No resource_set import is
introduced in this direct host source boundary.

## Separate-process evidence contract

local_controller_process_native_probe accepts a compiled orchestrator path and
uses real bounded child invocations (20s,64KiB capture each). It never imports the
in-process command adapter. All responses must keep V1 version/kind and execution
false; successful responses also retain controllerId and requestUid where
applicable. The fixture independently reads the exact source bytes at
<stateRoot>/journal/desired-input-objects/<sourceDigest>.sdn after submit and
compares both source content and hash, without a store helper oracle.

Further child invocations test exact UID/sourceDigest replay, changed-content
refusal, policy retention, cancellation source check and sticky cancellation,
then confirm runtimeState=unobserved and terminationObserved=false. No process
oracle treats metadata as a host preparation or provider launch.

## Provenance snapshots

Original source SHA-256 identities are retained below. HostConfig and workload
store are explicitly adapted; the remaining imported sources are exact copies.
The shared CI tracked diff from the original prototype was reviewed separately
before adoption; its180-line original diff hash is recorded below.

- `src/app/orchestrator/command.spl` original `abdfc136a34b77741692d52852ace2331efd54dbefb756171780ff479e186239`
- `src/app/orchestrator/explain.spl` original `b687c1bd7ad86084f8e3178b6a128caf6aa3937fb4b36ee1598a1ffe5b4176b4`
- `src/app/orchestrator/inspection.spl` original `74b85c23f421ec6a0589b8b460186c864f83a4b7c661a87654bbb875f1ab612c`
- `src/app/orchestrator/local_controller.spl` original `91b6fe81eb899205cb4bfccff395ebc6e86d8ef8bae3b34b67b0ebeb34d64f92`
- `src/app/orchestrator/main.spl` original `cf03767cbc8e5ac400d000e58b9e9dee681afa292af791035782f8cbeec5abb4`
- `src/app/orchestrator/validation.spl` original `c614111c75124571b1969301e4805f2fe3d4f8563b7baee35d6cc1294e1c3a73`
- `src/lib/common/contracts/orchestration/agent_policy_resolution_v1.spl` original `0689d3cf5167f7878199650fc5f9ee82cfa99bfef968af10b61ca234986d5e6b`
- `src/lib/common/contracts/orchestration/agent_policy_snapshot_v1.spl` original `2841938da6b575c0214ea1e4623c1b5b81b2130b70ffc6bf0d1ecf43b7e4c951`
- `src/lib/common/contracts/orchestration/agent_session_v1.spl` original `ea3467a5e84ac99ec2d787a1ab394e6899a1e5b7106e57e60e94a7d7557ac93b`
- `src/lib/common/contracts/orchestration/ci_v1.spl` original `8a76bf81c19c5f0f10a778af746b7bda88eaf2236cafedb058cc74c8be4fc11f`
- `src/lib/common/contracts/orchestration/desired_input_v1.spl` original `783bf9eee8491549c9899d092f3770d6c6c49d9a07b0cdcfdf03eaa84ff1607e`
- `src/lib/common/contracts/orchestration/execution_policy_v1.spl` original `c2bfd500f2f7145d643e21b694ba44a8ee8b0ba4890485be76795ad8a8b1844a`
- `src/lib/common/contracts/orchestration/host_config_v1.spl` original `103b5abd628c7ba73f96ff337a72c606a6064304b799e01d65c5d8beed7167d5`
- `src/lib/common/contracts/orchestration/resource_set_v1.spl` original `4924a68acdbaa49cc6f02d5e861ef1816b06ea91eb38cf7ca97b3be9e72b238b`
- `src/lib/nogc_sync_mut/orchestration/agent_policy_objects_v1.spl` original `148b0e12b5f809c8d123df3dedd013085d664c85ca3158ec7df7f22efe58aa1b`
- `src/lib/nogc_sync_mut/orchestration/assignment_commit_v1.spl` original `576a568613371e546da944465d2391b63c3d14f84cb3244ab1cbde39468f9459`
- `src/lib/nogc_sync_mut/orchestration/assignment_objects_v1.spl` original `27eb603ce28d62bc69eab3d1011defbcf97f9026334c2410ab66d3424ea6eebd`
- `src/lib/nogc_sync_mut/orchestration/desired_input_objects_v1.spl` original `abea526b79ab205a1ab9bcea9e3c0729c3e8ab9740c782c4ebe45bef56a41eb3`
- `src/lib/nogc_sync_mut/orchestration/workload_store_v1.spl` original `e8c5f340599eedf9f8e82b968ea9dfae6d45594a6c53e37d81488e9e535c3873`

Original CI diff SHA-256: `2790ef88e7c675a76960cbefd0900ac1c055c0b18238dddff158af7d3f07c777`.

Adapted main resource_set_spec.spl source hash: `933924bc76fca48948f41479eed57b5977020089f3bef0d01aff53469904d49b`. Only focused CI singleton/prefix cases are adopted, with existing tracked CI fixtures.

## Validation limits and ownership

Source/import/provenance checks are static. Separate-process fixture, direct
HostConfig fixture, CI prefix fixture, admitted SSpec, generated manuals, coverage,
core/MCP/LSP and provider tests remain **NOT_RUN**. Manuals are authored and
explicitly not generated execution evidence. No compiler/crypto source changed
and no build is performed here. The current diagnostic producer's secure_memory
fill_span failure blocks native execution until independently changed producer
dependencies justify another authorized build; this change claims no repair.

Sol owns this metadata implementation; Astra reviews exact commit and coordinates
later signed host composition; root owns scarce builds and landing. Additional
sidecars:N/A. Full distributed acceptance still needs an external controller-host
invocation and provider nonce/native-identity inspection; missing live Podman is
BLOCKED, not an inferred success from these metadata fixtures.
