# Workspace storage acceptance and remaining implementation

This lane implements native storage admission/readback and a read-only Linux
release observation. The existing host operation journal is the sole capacity
writer; Host owns its versioned storage intent/charge extension. No second ledger,
automatic workspace deletion, quota mutation, chmod, or privilege setup is added.

The focused native negative fixture is
`src/runtime/test/workspace_storage_owner_v1_selfcheck.c`. Its one actual Linux
run passed 73 checks. The five modern SSpec narratives and authored manual are
`test/01_unit/lib/storage_roots/workspace_storage_owner_v1_spec.spl` and its
`doc/06_spec` mirror. Simple execution/docgen remain NOT_RUN.

| Required real acceptance | Mandatory prerequisite | State |
|---|---|---|
| XFS exact project identity, enforcement and hard-byte readback | Protected configured XFS mount, delegated project, admin policy and native quota access | BLOCKED platform fixture; source present |
| EDQUOT at real block boundary, independent readback | Isolated disposable charged project and explicitly authorized writer | BLOCKED; no byte-count substitute |
| Disabled enforcement, wrong project/mount/inode, symlink/replacement refuse | Same native fixture plus controlled policy/identity changes | Authored plan, NOT_RUN |
| Existing dirty data and unknown cleanup stay charged | Same host journal with correlated storage request | Host integration pending |
| Exact unlinked Linux inode plus project blocks/inodes zero releases native owner once | Authorized external exact cleanup; retained native lease | Source present, positive NOT_RUN |
| Restart with already absent workspace reconciles exact retained charge | New authorized recovery proof bound to immutable project/workspace | IMPLEMENTATION_PENDING; current conservative refusal |
| Windows GUID/FileID/creation time, protected DACL, exact volume length | Approved disposable dedicated NTFS volume and installed authority | Source present, Windows NOT_RUN |
| Windows real over-capacity refusal | Explicitly authorized write inside the dedicated bounded volume | BLOCKED platform fixture |
| Windows exact-volume disposal or independently proved empty release | Explicit host retention/deletion policy and immutable volume ownership | IMPLEMENTATION_PENDING; current release unsupported |
| Full host reserve, execution, dirty retention, authorized cleanup, release | Host same-ledger V2 integration and both platform qualified owners | INCOMPLETE |

Execution is finite: one admitted runner/docgen run after compiler prerequisites,
then each configured native positive case once. Any retry changes source or
collects new evidence; six-cycle cap applies. All local processes share CPU
affinity `0-4` (five total), with bounded wall time and memory. Current source
checkpoint does not authorize privileged provisioning or destructive effects.

Independent Astra source review precedes landing. Native negative PASS is neither
compiler admission nor full provider/system qualification. Full Windows lifecycle
and full original orchestrator acceptance remain active requirements.
