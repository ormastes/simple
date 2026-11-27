# Actual Windows current-process principal owner V1

Status: **AUTHORED_NOT_RUN**. Mirrors
`test/03_system/tools/windows_local_process_principal_v1_spec.spl`.
No native fixture, compiler, runtime, engine or doc generator ran.

The zero-identity-input factory queries the actual current process primary
token. Its opaque owner retains a token HANDLE, bounded heap arena and private
canonical-thread slot/generation. Public snapshots are diagnostic data and
cannot construct the owner or authenticate a daemon client.

| Requirement | Authored actual native assertions |
|---|---|
| REQ-LOCAL-PROCESS-PRINCIPAL-001 | Reobserve the same actual process/token identity; require canonical `windows:S-1-...`, actual process/thread IDs and actual boot/logon namespace. Close then reject copied stale ownership. |
| REQ-LOCAL-PROCESS-PRINCIPAL-002 | Two real owners preserve stable principal spelling while their generations/live identity digests differ. A real same-user `ImpersonateSelf` token is refused; restoring fixture context does not resurrect a quarantined owner. |
| REQ-LOCAL-PROCESS-PRINCIPAL-003 | A real OS thread's cleanup attempt returns retained without losing the original owner; the original thread revalidates and closes it. Native release failures remain separately unexecuted fault-injection obligations. |

`current_v1()` refuses every thread token unless `OpenThreadToken` reports exact
`ERROR_NO_TOKEN`. Production never impersonates, elevates or calls
`RevertToSelf`; only the isolated test fixture restores its own deliberately
created context. TokenUser SID and TokenStatistics TokenId, AuthenticationId,
ModifiedId, actual process creation FILETIME, actual process/thread IDs and
kernel boot identifier are pinned and rechecked. A replaced/modified token or
changed context quarantines the owner. Stable policy membership uses
`principal_id`; a PID-derived live identity never becomes a durable principal.
Installed membership uses the exact prefixed spelling `windows:S-1-...` or
`linux:uid:<decimal>`. Bare SID strings in the older pure codec's metadata
fixtures establish neither native identity nor actual policy membership.

The fixed Win64 boot-environment query uses native information class 90 and
requires the exact 32-byte layout plus nonnil BootIdentifier. Unsupported
responses refuse; there is no registry counter fallback. Its ABI, OS support,
link route and retention behavior remain unqualified.
BootIdentifier is namespace evidence; its equality alone never proves a unique
boot incarnation, workload absence or permission to adopt retained execution.

Microsoft documents the [token statistics](https://learn.microsoft.com/windows/win32/api/winnt/ns-winnt-token_statistics)
and [process creation time](https://learn.microsoft.com/windows/win32/api/processthreadsapi/nf-processthreadsapi-getprocesstimes)
contracts. The native boot-environment layout follows the primary
[System Informer phnt headers](https://github.com/winsiderss/phnt/blob/master/ntexapi.h).

Additional required isolated fixtures remain **MANUAL_NOT_RUN**: actual primary
token replacement, token ModifiedId change, alternate/nil boot response,
process-incarnation mismatch, allocation failure and failed CloseHandle or
HeapFree followed by exact cleanup retry. No injection seam or synthetic
capability constructor is added to production to make those cases pass.

This owner authenticates the current process only. Kernel-authenticated daemon
peer production, installed standalone policy membership, genuine migration
fence, durable resource admission, provider execution, terminal adoption and
absence-proven settlement are separate requirements. A daemon must never pass
its own process principal as proof of a client identity.
