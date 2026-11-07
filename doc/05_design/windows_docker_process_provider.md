# Windows Docker process provider detail design

Status: AWAITING_VERIFICATION. All execution gates are NOT_RUN.

`docker_contract_v1.spl` owns policy/request validation, request digests and argv.
`docker_codec_v1.spl` strictly encodes/decodes canonical SDN against trusted policy;
unknown, duplicate, missing, wrongly typed or digest-mismatched fields are refused. `docker_runtime_v1.spl` owns command execution, exact-ID
lifecycle, bounded local records and recovery. Additional Windows-only modules
may separate argv and observation helpers without changing common contracts.

Admission precedes execution. Native IDs must be full lowercase hexadecimal
Docker identities. Labels bind workload UID, attempt, operation, boot, generation
and semantic request digest. Inspection must match image ID/reference, actual
process isolation, ContainerUser and admitted resource/network configuration.
No caller-provided observed state is accepted as native authority.

Prepared intent and native creation are separate stages. Create ambiguity is a
retained blocked state, not permission for retry. Error output is diagnostic;
nonzero inspect alone is not proof of absence. Recovery requires an exact retained
ID and revalidation of the original request. A provider recreation cannot infer
that an old attempt is safe to create without the caller's durable journal.

Scripted tests inject operation, executable, exact argv and bounded results.
Unexpected or exhausted scripts fail; success fixtures are explicitly synthetic.
The system spec describes end-user consequences with steps and real assertions.
Its manual mirror is authored pending the unavailable admitted docgen runner.
No generated score, coverage percentage or Windows pass is claimed.

The semantic request digest excludes operation ID; the exact operation label,
record and recovery intent separately enforce operation ownership. Deterministic
create names bind workload/attempt/engine/boot/generation and exclude operation ID,
preventing a changed operation ID from naming a second same-attempt container.
All mutable provider state remains a bounded cache; callers cannot omit durable
replay admission merely because a deterministic name exists.

Native capture copies only SystemRoot, TEMP and TMP from explicit policy. It does
not inherit Docker context/host/TLS/config/plugin environment variables. Docker's
executable and local pipe are explicit arguments. Executable path sealing is not
provided: this is a trusted-administrator process boundary.

## V2 API source integration

`simple_container_adapter_v2.spl` implements the common factory, projection,
apply/read, intent/recovery and independent absence ports. `docker_policy_codec_v1`
keeps trusted canonical policy separate from request input. Semantic/provider
digests use the common raw64 SHA256 spelling; Docker image IDs/references retain
their required `sha256:` spelling. Operation identity remains independently bound.
`docker_scope_v2` binds explicit labels and exact scoped inspection.

`windows_host_identity_v1` owns bounded direct registry/native-architecture reads;
`windows_service_incarnation_v1` owns 32 CNG random bytes for one service start.
Neither fabricates an OS boot incarnation. `docker_inventory_v2` brackets bounded
managed inventory with engine/membership observations and rejects incomplete rows.
Its 30-second acceptance budget detects late results but cannot preempt governor
slot waiting; it is not a hard response deadline.

The persistent service-incarnation owner is implemented by the shared host lane;
this source retains a fail-closed activation gate until that owner is supplied.
All native Windows and common-API lifecycle qualification is still NOT_RUN.

## Explicit execution projection amendment

The Simple Container action projection exposes the actual entrypoint plus typed
arguments and an explicitly requested absolute working directory. A missing
directory remains supported by the historical version-one lifecycle but cannot
produce a resolved action projection. Version two adds `workingDirectory`, binds
it in the semantic digest, emits Docker `--workdir`, and checks the actual
`Config.WorkingDir` before accepting creation. No image default is guessed. The
mount projection is empty because this provider has no workspace mount effect.

The common runtime identity uses native engine `docker`; the ownership/provider
label remains `windows-docker-process-v1`. A terminal inspection does not replace
the actual Docker wait command needed for an execution receipt.

These amendments and their executable assertions remain NOT_RUN: no qualifying
Windows Docker host or available admitted Simple compiler run was supplied.
