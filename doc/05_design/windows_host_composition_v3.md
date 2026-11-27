# Windows deployment-backed Host composition V3

Status: **AWAITING_VERIFICATION — source only, NOT_RUN** (2026-11-14).
The closed runtime/bootstrap campaign has not been restarted. This document
does not qualify Windows deployment, filesystem crash recovery, Docker effects,
or the complete orchestrator/Caret workflow.

## Accepted boundary

The existing protected `HostWindowsDeploymentOwnerV2` now opens its fixed
`journal` child through a retained native store. `HostWindowsLocalRootV3` keeps
that deployment, the actual common Container service owner, the existing
`HostCapacityOwnerV1`, and the existing startup reconciliation turn together.
`HostLocalRootV3` preserves Linux and Windows provenance as distinct variants.
No Linux enrollment or boot identity is manufactured for Windows.

The Windows provider's real fresh service incarnation and inventory enter
`host_service_reconcile_v2` after the actual journal writer is acquired. Old
executing records become outcome-unknown through the existing journal engine.
Uncertain resource charges survive startup. The signed broker partition is
subtracted once using `host_service_allocatable_v2`. Provider launch admission
requires the actual retained reconciliation receipt; a status string is not
an admission token.

`HostServiceDomainV3` consumes this root for status, validation and signed
preparation. Its owned-execution follow-up adds an explicit effect-worker port
and signed parent-budget hook; see `host_execution_store_owned_v3.md`.
The canonical orchestrator command consumes that domain through
`host-service`; platform selection stays in the library. Persistent connection
owners can use the same root instead of opening a second journal writer.

## Storage and ownership

`WindowsJournalStoreV1` has no pathname constructor. Its factory consumes the
actual retained protected deployment directory capability and opens only the
fixed `journal` child. Native handles, ACL checks, ancestor identities,
root-relative child opens and the stable exclusive parent lock remain native
generation-owned state. Stage files, failed closes and other temporary resources
remain attached to that state after errors. Native close distinguishes a stale
copy from a resource-bearing pending close.

The existing segmented WAL and distributed-operation journal receive an
optional actual Windows store. Their record formats, replay fold, transition
rules and capacity ledger remain shared. Linux callers retain default storage.
Windows CURRENT comparison and replacement occur together under the native
store lock; a separate read followed by replacement would permit stale aliases
to overwrite a newer commit. Immutable objects and Host archives use
nonreplacing publication and exact readback. Reads distinguish exact absence
from denied, corrupt or uncertain observations.

Relative paths are bounded to four components, 128 bytes per component and
512 bytes total. File payloads are bounded to 8 MiB. Store/native registry
capacity is bounded and exhaustion refuses admission. The guarantees remain
**process-crash-v1**; there is no power-loss durability or performance claim.

New primary connection consumption can return an opaque native receipt only
after a newly published fixed consumption record under the exact executing
helper operation. It binds the actual store generation, exact bytes and a
unique receipt sequence. A claim consumes it before success; replay, readback
or a decoded record cannot recreate it. This storage receipt is not itself a
signed execution grant: the Host connection owner must verify the independent
grant/approval and the lower connection admission must correlate the expected
plan and deadline. The parallel Windows connection lane owns that consumer.

## Consumed command

Trusted local administrator syntax:

```text
simple-orchestrator host-service <backend> <installed-root-or-parent> <policy-pin-or-dash> <binding-file-or-dash> <action> <operation-id-or-dash> [payload-file]
```

Linux uses `linux-podman` and `- -` for the two Windows enrollment arguments.
Windows uses `windows-docker-process`, the administrator-selected installed
machine parent, its policy digest and the signed enrollment binding file.
The binding file is data until the retained deployment validates it against
the protected installed policy, claim, manifest, metadata and native provider.
These startup arguments are never service request fields. `host-status` uses
`-` as operation ID and no payload; `host-prepare` and `host-validate` require
an operation ID and payload file. The owned-execution follow-up also admits
`host-execute` through the explicit effect-worker boundary and
`host-parent-budget` through owned signed-budget storage. Cleanup remains refused
by this finite command. The nonblocking control callback still refuses effects.

A finite command closes its own writer after its response is formed. A later
Windows service start obtains a new incarnation and reconciles old preparations;
the finite command is not a durable running service or an execute permission.
The caller retains typed deployment/journal cleanup after every partial close.

## Remaining integration and qualification

Windows completion does not fall through to Linux pathname evidence. It remains
charged uncertain until the connection lane supplies the exact typed pipe-closed
validator and publication. Linux-only exec-child/installation evidence in a
Windows journal refuses startup instead of being interpreted under weaker IO.
The parallel connection lane also owns helper packet migration, parent runtime
resolution, common terminal V2 and the backend-neutral smux consumer.

Authored guards and Linux filesystem regressions do not cover successful signed
Windows deployment, native ACL mutation, restart reconciliation, inventory drift,
post-effect Host publication failure, or provider activation. Those integrated
paths are **NOT_COVERED / NOT_RUN**, with the acceptance inventory in
`doc/03_plan/sys_test/windows_host_composition_v3.md`. Native fixture scenarios
are authored separately and require actual protected Windows directories; an
unsupported host is not a passing test. Generated manuals have not been run
through docgen. No coverage percentage is claimed.

## Native boundary proposal

The necessary C-private exports own native handle generations or operate under
that exact owner's lock: `rt_windows_journal_open_v1`, `live_v1`, `read_v1`,
`publish_v1`, `replace_v1`, `compare_replace_v1`, `close_v1`, and
`consumption_claim_v1` (all share the `rt_windows_journal_` prefix). These cannot
be replaced by a Simple wrapper that accepts raw handles without losing the
private native authority boundary. Allocation reuses existing `rt_alloc` /
`rt_free`; no new allocation-only export is proposed. The exact C-only policy
admission requires repository-owner approval; this patch does not change the
ratchet, baseline or allowlist. Source-only authorization does not exempt it.

Microsoft documents root-relative rename and replacement behavior in
[FILE_RENAME_INFO](https://learn.microsoft.com/en-us/windows/win32/api/winbase/ns-winbase-file_rename_info),
and lock behavior in
[LockFileEx](https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-lockfileex).
Those API contracts inform the implementation; they do not substitute for
qualification on the supported Windows/filesystem configuration.
