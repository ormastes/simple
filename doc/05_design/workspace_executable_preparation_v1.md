# Pinned workspace executable preparation

Status: source implementation with 163 dynamic native component checks passed.
The first real native run exited 77 because the mount parser rejected valid
unrelated nsfs metadata. The corrected binary then hit a harness logical-file
limit; the same binary passed after that limit allowed the deliberate sparse
size-boundary case. Both blocked attempts are retained. No full preparation
success or permission-effect qualification is claimed.

The mechanism is
`std.nogc_sync_mut.storage_roots.workspace_executable_preparation_v1`.
The public adapter requires the existing storage lease, the retained native
primary-user observation, a distinct `WorkspacePreparationDeadlineV1`, the
expected stage digest/operation, relative input/output roots and an exact
manifest entry. It always returns both owners. A decoded receipt is evidence;
it is not authorization and cannot reconstruct either native lease.

## Authenticated stage boundary

The common/Host consumer must authenticate the distinct `workspace_prepare_v1`
operation in the existing host journal, recompute its exact stage digest, retain
the admitted immutable-image keeper phase and verify the exact executable
manifest. That digest covers keeper/runtime identity, exec birth, storage and
mapping bindings, and input/output/executable selection. It is neither the
workload request digest nor the provider mapping-binding digest. The native
boundary receives stage digest/expiry separately from the retained mapping
binding; it performs no signature verification or independent journal write.

The explicit profile uses `/simple-build/inputs` read-only and
`/simple-build/outputs` writable. Allowed executable entries are `producer.exe`
and `tools/simple` relative to inputs. There is no secret entrypoint override,
caller-selected chmod mode, recursive permission change or arbitrary workload
before preparation is retained. The exact execution owner must recheck its own
fresh start authorization afterward; preparation does not launch a process.

## Native checks and effect

- Loan the existing storage and observation slots under the registry mutex;
  mark both busy so release/close cannot race. Hashing occurs outside that mutex.
  No new registry, raw FD accessor, cleanup authority or capacity ledger appears.
- Reobserve actual XFS quota enforcement and primary mapping. Require target
  effective and filesystem UID/GID to equal the actual observer's credentials.
- Open every host relative component beneath the retained workspace using
  nofollow handles. Require the same XFS project/device, trusted owner, owner
  traversal, no foreign write access and no mount crossing. Separate pools and
  nested host bind mounts are currently unsupported, not presumed equivalent.
- Open fixed guest paths through the retained primary proc root. Require native
  inode/owner agreement with the host input/output directories; check target DAC
  traversal without credit from caller capabilities or supplementary groups.
- Read bounded actual host/guest mountinfo (256 KiB, 512 rows). Locate roots using
  real fd mount IDs and kernel fd-path observations. Pin initial mount-namespace
  descriptors through the operation. Require exact read-only input/writable
  output mounts, disjoint actual filesystem roots, and no writable same-device
  mount overlapping the input root in either direction. Unrelated opaque nsfs
  roots are metadata only; selected/same-device security roots must be canonical
  absolute paths. The executable may not cross a nested guest input mount.
- Pin a regular, single-link, host-owned file with no setuid/setgid/sticky or
  foreign-write bits. Stream at most 1 GiB through the existing SHA compression
  owner. Require exact expected digest and stable identity/size/metadata.
- Add only owner execute, preserving other permission bits. Recheck actual mode,
  digest, identities, path membership, project, mapping, read-only target view
  and mount snapshots after the attempt. Any post-attempt failure is uncertain;
  the code does not undo permissions, delete files or release capacity.

Namespace/mount snapshots detect changes; they do not seal a filesystem against
an authorized host administrator. The retained Host staging owner must exclude
concurrent source writers, and the immutable keeper must have no writable route
to producer inputs. The native alias checks enforce the observed mount topology;
they do not replace the authenticated phase exclusion or prove future exec bytes.

## Deadlines and retained outcomes

`WorkspacePreparationDeadlineV1` carries the signed preparation-stage digest,
operation ID and Unix expiry after trusted Host verification. At native entry,
monotonic time is sampled before real time; remaining authorization becomes a
monotonic bound with an additional 60-second processing cap. Hashing checks the
monotonic deadline, and actual real time is checked immediately before chmod.
Clock rollback during the operation cannot extend the sampled monotonic window.
An expired/refused operation returns retained owners. Post-effect uncertainty
and malformed/absent native results set `recovery_required`; only a fully checked
receipt has state `prepared`. That state is not workload completion or cleanup.

Windows preparation is explicitly unqualified here. Its selected-user ACL and
exact-volume lifecycle require a separate actual platform owner. Neither Linux
mode bits nor a copied owner observation supplies Windows authorization.

## Evidence limits

The new native selfcheck exercises independent SHA vectors, size/deadline bounds,
real mountinfo/statx/namespace observations, target traversal predicates and
invalid-owner refusal while preserving its own abc/0600 fixture. It never
fabricates admitted XFS/quota facts, read-only container mounts, keeper authority
or successful chmod. Full positive preparation remains blocked on that actual
configured fixture. Simple deadline/ABI/adapter execution and generated docgen
remain NOT_RUN. The historical observer 61 and storage 73 evidence is separate and
was not repeated to manufacture a current whole-system pass.

The 163-check evidence predates the separately identified inherited-registry
mutex/process-origin repair. It does not establish fork-child capability
isolation; that regression requires its own source-bound fixture.
