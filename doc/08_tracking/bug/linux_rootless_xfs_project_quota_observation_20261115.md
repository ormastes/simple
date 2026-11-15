# Rootless service cannot query the existing XFS project-quota lease

Bug ID: `linux_rootless_xfs_project_quota_observation_20261115`
Status: **OPEN — SOURCE-CONFIRMED PERMISSION MISMATCH; NATIVE NOT_RUN**
Scope: actual Linux workspace quota admission/refresh for the selected dedicated
nonroot service UID and rootless Podman deployment.
Owner of this report: `linux_machine_storage_sol_20261115`.
Tracking: uniquely owned report; no shared bug database was edited.

The existing workspace backend measures project quotas with
`quotactl_fd(QCMD(Q_XGETQUOTA, PRJQUOTA), ...)`. The selected machine-policy
owner requires an actual nonroot service process with zero permitted and
effective capabilities. The kernel permission path requires `CAP_SYS_ADMIN`
for this project-quota query. Filesystem ownership and an administrator-set
project quota do not supply that syscall privilege. An actual quota lease
cannot currently be admitted/refreshed by this selected service process through
the existing direct native path.

This is a source-level blocker, not an executed failure report. No host kernel,
native fixture, quota syscall, build, Podman or runtime campaign was run. The
expected native outcome on the cited standard kernel path is `EPERM`;
the actual host result remains **NOT_RUN**.

## Actual production call chains

The fixed administrator profile is read through
`LinuxMachinePolicyOwnerV1.read_workspace_profile_v1()` in
`src/lib/nogc_sync_mut/io/linux_machine_policy_owner_v1.spl:23`.
`linux_workspace_storage_request_v1()` in
`src/lib/nogc_async_mut/container/providers/linux/workspace_installed_profile_v1.spl:26`
selects `linux-xfs-project-v1` and the installed pool/workspace/project/hard-byte
pins. This is configuration correlation, not native quota enforcement proof.

Admission follows the existing native owner, without a privilege broker:

1. `workspace_storage_admit_v1(request)` at
   `src/lib/nogc_sync_mut/storage_roots/workspace_storage_owner_v1.spl:73`
   calls `rt_workspace_storage_open_v1(...)`.
2. `rt_workspace_storage_open_v1` at
   `src/runtime/runtime_workspace_storage_v1.c:297` enters
   `ws_open_or_recover_v1` at line 256, which calls `ws_native_open_v1`.
3. `ws_native_open_v1` at
   `src/runtime/runtime_workspace_storage_linux_private.h:86` retains and
   validates the actual workspace, XFS/project identity and configured pins,
   then calls `ws_linux_measure_v1` at line 103.
4. `ws_linux_measure_v1` at line 31 queries project accounting/enforcement
   status using `Q_XGETQSTATV`, then queries the actual project hard limit and
   usage using `Q_XGETQUOTA` with `PRJQUOTA` at line 40.
5. `ws_quota_v1` at line 23 invokes `SYS_quotactl_fd` on the retained parent
   descriptor. Failure returns its native errno; admission closes its partial
   native candidate and returns a negative error. The Simple owner refuses a
   nonpositive token. A cached profile cannot substitute for that failed lease.

Refresh has the same privilege dependency:

1. `workspace_storage_observe_v1(lease)` at
   `src/lib/nogc_sync_mut/storage_roots/workspace_storage_owner_v1.spl:68`
   calls `rt_workspace_storage_observe_v1` at
   `src/runtime/runtime_workspace_storage_v1.c:307`.
2. Its `ws_native_observe_v1` call rederives actual retained root/project
   identity and invokes `ws_linux_measure_v1` again at
   `src/runtime/runtime_workspace_storage_linux_private.h:117`.
3. A measurement failure yields no successful native receipt; the Simple
   receipt decoder refuses it. A recovered retained token is cleanup authority
   and does not establish a current enforceable-quota observation.

Both new supporting owners depend on this current native observation:
`workspace_source_sample_v1` in
`src/lib/nogc_async_mut/container/providers/linux/workspace_mount_owner_v1.spl:84`
and `linux_workspace_exclusion_probe_v1` in
`src/lib/nogc_sync_mut/io/linux_machine_workspace_exclusion_v1.spl`.
Their source acceptance does not make the blocked upstream quota lease exist.

## Exact credential mismatch and kernel evidence

The selected machine-policy factory requires real UID equal to effective UID,
both nonzero, and real/effective GIDs equal. Its genuine current-thread procfs
status check requires all real/effective/saved/filesystem IDs to match those
credentials and `CapInh`, `CapPrm`, `CapEff` and `CapAmb` each to be zero:
`src/lib/nogc_sync_mut/io/linux_machine_policy_owner_v1.spl:267`, the admission
check at line 330 and the repeated check at line 457. Root callers and a
capability-bearing service process are outside this admitted process model.

The primary kernel source's `check_quotactl_permission` handles
`Q_GETQUOTA`/`Q_XGETQUOTA` by exempting only a caller's own **user** quota or
an eligible **group** quota. `PRJQUOTA` takes the capability-required path and
returns `-EPERM` without `CAP_SYS_ADMIN`. The descriptor syscall uses the same
quota permission machinery; retaining an FD does not delegate that capability.
`Q_XGETQSTATV` itself is in the no-special-privilege branch, so the specific
blocker is the later project usage/limit query. See the immutable
[Linux kernel quota permission implementation](https://kernel.googlesource.com/pub/scm/linux/kernel/git/torvalds/linux.git/+/26c9342bb761e463774a64fb6210b4f95f5bc035/fs/quota/quota.c).

There is no new implementation or privilege change in this report. The
machine-policy credential/namespace checks, actual quota observation requirement
and current native error handling remain intact.

## Candidate narrow observation boundary — design only

A separately approved privileged observation boundary could let the actual
unprivileged service query an administrator-selected project without granting
that service general mount/quota administration. Prefer an existing approved
administrator/supervisor process and authenticated local transport when they
can provide the required ownership semantics; this report does not authorize
a new daemon, setuid program, runtime export or allowlist change.

The privileged side would resolve an installed closed profile to retained
filesystem/workspace descriptors, verify actual XFS enforcement and query the
specified project. Caller-supplied paths, project numbers or quota limits must
not select privileged resources. It must authenticate the actual service
principal and process/namespace scope, bind exact machine/profile/request
digests, physical device/inode/generation, project and hard limit, and retain
the actual query/session owner through refresh and cleanup.

The unprivileged side needs a reviewed typed owner tied to that live
authenticated session, server incarnation, actual workspace identity and
current observation. Copied SDN, a signed historical receipt, an installer
success record or an ordinary lock cannot manufacture a live quota lease.
Existing direct-native lease ownership cannot be silently reconstructed from
broker metadata; any adapter and ABI change requires explicit separate review.

Loss of the boundary, changed quota/enforcement, replaced root, changed server
incarnation or uncertain cleanup must fail closed and preserve actual retained
owners/charges. The boundary should query only; installation and quota mutation
remain administrator operations. This design candidate is unselected and
unimplemented. Its feasibility, threat model and maintenance cost need review
before implementation authorization.

## Required honest acceptance

- **Positive actual-service gate:** the actual dedicated nonroot service,
  still passing the genuine machine-policy credential/namespace checks with
  zero permitted/effective/inheritable/ambient capabilities, must acquire and
  refresh an enforceable workspace quota through the explicitly approved
  boundary using production Simple entrypoints. A privileged test process
  querying quota on its behalf without that production boundary is insufficient.
- **Real enforcement:** use a disposable administrator-prepared XFS project
  fixture with accounting and enforcement enabled, actual project inheritance,
  pinned root identity and hard limit. Exercise real writes against the limit,
  verify the kernel refuses excess allocation, and correlate actual usage and
  quota observations before/after. Configuration bytes alone are insufficient.
- **Fresh native ownership:** prove real pool/root/project/hard-limit
  correlation and current server/session incarnation; physical mount aliases
  must not split the exclusion/budget scope. Refresh must reject root,
  generation, project, policy, hard-limit or enforcement changes.
- **Authority and cleanup negatives:** reject an unauthorized UID/process/
  namespace, caller-selected resource, copied/stale receipt, expired or replaced
  server/session and lost observation boundary. Preserve partial native owners
  and existing charges on every uncertain path; do not release quota because a
  query failed or a workspace path was absent.
- **Evidence and admission:** record exact admitted compiler/runtime, actual
  service credentials, kernel/filesystem, commands, exit status and native
  observations under the newly authorized bounded campaign. Existing source
  reviews, authored specs and root-only probes remain distinct from this gate.

Until that gate passes, the configured XFS positive fixture remains
**AUTHORED_NOT_RUN / NOT_ADMITTED** for the selected rootless service model.
The cooperative exclusion helper can be reviewed and landed as conditional
support; it is not a completed Podman workspace or execution milestone.
