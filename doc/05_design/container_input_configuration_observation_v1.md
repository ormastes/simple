# Actual input configuration observation

Status: SOURCE_AUTHORED_NOT_RUN, initial source revision. The existing six-cycle
qualification limit remains exhausted; this work starts no compiler, runtime,
engine or native campaign and adds no native export or executor.

`simple_container_input_configuration_observe_v1(owner, original_request)` returns
`ContainerExecutionInputConfigurationTurnV1 {owner, observation?, error}`. The
updated genuine Simple Container owner is returned on every outcome. Its
observation is DATA: `configuration` is the unchanged configuration V1 snapshot,
followed by mandatory `open_stdin`, `tty`, `stdin_once` booleans and the separate
`input_configuration_digest`. A caller-created DATA record is never accepted as
the actual producer or an admission/task capability.

The additive read action is `input-configuration`. Existing adapter ownership,
original request/digest, current scope/policy and runtime generation checks run
before the retained runtime captures container/image/container through its
existing executor. The image query uses the exact observed config ID. The new
container query is a trusted fixed extension of the old fourteen-field template:
it adds JSON `Config.OpenStdin`, `Config.Tty` and `Config.StdinOnce`, all at the
same object level. No caller template, result or native ID factory is introduced.

Strict parsing retains the existing 1 MiB native source and depth-three bounds.
The exact seventeen fields and all three booleans are required; missing, null,
string or numeric flags produce explicit
`container-input-configuration-native-boolean-unavailable` refusal rather than
false. Duplicate/unknown/deep/oversized native replies also refuse. The parser
removes only these three known flag keys from private JSON DATA and delegates
the remaining fourteen fields to the unchanged V1 parser. Image/config versus
repository-digest correspondence, environment privacy, argv/mount bounds and
runtime-label checks therefore remain the V1 rules.

Both container captures must match in their complete selected V1 configuration
and all three flags. `StdinOnce` is recorded and bound even when unused by an
engine; changing it during the observation still invalidates the snapshot.
The mandatory fields are present as booleans in the primary
[Podman v5.2.5 schema](https://github.com/podman-container-tools/podman/blob/v5.2.5/libpod/define/container_inspect.go)
and [Moby v28.0.1 schema](https://github.com/moby/moby/blob/v28.0.1/api/types/container/config.go).
Podman's StdinOnce field is unused: none of these facts alone proves stdin EOF,
kernel descriptor state, first task birth, target namespace or future behavior.

The outer canonical SDN record has a separate kind/version and seven keys:
kind, version, configuration, openStdin, tty, stdinOnce, inputConfigurationDigest.
`configuration` contains the exact old canonical V1 wire as text. The outer SHA256
binds that complete wire and all flags, with its own digest field zeroed. Decode
validates the V1 component, exact canonical outer bytes and outer digest. The
outer record is bounded to 1 MiB and refuses overflow without truncation.
Environment values remain private behind V1 names/digests; native/parser errors
do not disclose raw query output.

The old V1 contract, JSON helper and query module remain untouched. Its actual
entry selects the old fixed command/parser/output branch; its native command,
wire and digest do not acquire an input flag or an implicit false default. New
private capture selection shares the existing native sequence, retaining the
same executor and owner lifecycle. Windows remains below 800 lines; historical
oversized Linux runtime and Windows adapter receive only bounded forwarding
changes. Canonical native command slots and capture cleanup are unchanged.

The new genuine fresh Linux owner is a separate route. Its owner worker reserves
an early dispatch that returns
`linux-fresh-workload-input-configuration-unavailable` and the same owner until
an actual fresh-owner producer exists. It must never fall through the legacy
per-workload journal. This slice implements legacy Linux and Windows producers;
it does not claim positive fresh Linux input support. The genuine fresh-owner
negative fixture belongs to that worker and remains NOT_RUN/NOT_COVERED here.

The separate task-input restriction owner may require actual OpenStdin=false and
Tty=false for an explicit Argv profile, with StdinOnce recorded only. That owner
must call this actual port in the same genuine current-create-to-start lifecycle;
request terminalMode DATA, caller booleans or a separately supplied observation
are insufficient. This slice changes no Host constraint, signing, admission or
task route and enables no Argv task by itself.

Seven authored source scenarios exercise actual common API/scripted provider
paths and pure wire validation. Every scenario is NOT_RUN. Independent Astra
source review is required before landing; none of the source assertions qualifies
native input behavior or resets the prior verification-cycle count.
