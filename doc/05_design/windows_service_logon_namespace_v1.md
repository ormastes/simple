# Retained Windows Service-logon namespace producer V1

Status: SOURCE_AUTHORED_NOT_RUN. No Windows/native, linker, runtime, ACL-fault,
service deployment, or stock OpenSSH interoperability qualification is claimed.
This implements the producer portion of
`windows_ssh_retained_credential_projection_v1_20261115.md` (design SHA256
`52d56b0d2f85ef0c406c7af6f09770b1ae2c5bc108b08e098513733f8ef2d17c`).
Existing R2 generic credential-store path/preflight refusal is unchanged.

## Boundary and deployment

The zero-argument factory admits only the actual current Win64 process under
an LSA Service logon (numeric type5), on the canonical native Windows thread,
without impersonation. Interactive, network, batch, missing LSA data, and
unsupported native object queries fail closed. A SYSTEM identity whose actual
LSA record does not report Service5 is also refused; no SID substitutes for
the required logon type. An external native runner must be launched under a
genuine dedicated Service5 logon to qualify this path.

The minimum trusted authority is the actual process user, LocalSystem and
Builtin Administrators. Their ability to change namespaces/ACLs or compromise
the service is outside this deployment boundary. There is no same-authority
isolation claim and no claim of full interactive-client parity.

`WindowsLocalProcessPrincipalV1` is retained, reused and closed last. Its actual
identity includes token user, token LUIDs, process creation and kernel
BootEnvironment GUID, with no-impersonation rechecks. This leaf does not use
the Windows boot counter, caller identity facts, guessed session paths, or
saved PID adoption. Its additional retained process token is queried for
actual TOKEN_USER, TOKEN_STATISTICS AuthenticationId and TokenSessionId;
`LsaGetLogonSessionData` must match SID, AuthenticationId and session and
report Service5. The principal identity is correlated before and after those
queries. The retained LSA allocation and token remain cleanup obligations.

## Frozen public interface

Module: `std.nogc_sync_mut.io.windows_service_logon_namespace_v1`.

| API | Result |
| --- | --- |
| `windows_service_logon_namespace_open_v1()` | OpenTurn `{owner?,ready,error}` |
| `windows_service_logon_namespace_step_v1(owner)` | same OpenTurn |
| `windows_service_logon_namespace_current_v1(owner)` | `Result<(),text>` |
| `windows_service_logon_namespace_candidate_path_v1(owner,native_root)` | `Result<text,text>` |
| `windows_service_logon_namespace_close_v1(owner)` | CloseTurn `{owner?,completed,error}` |

The opaque `WindowsServiceLogonNamespaceOwnerV1` contains only a private
canonical slot/generation. Every entry checks actual native canonical thread
before lookup and actual process/thread origin immediately after lookup.
Known closed aliases report known completion; unknown/stale origins retain
the supplied owner and never fabricate a release. The nonreused registry is
bounded to32 live owners and100000 lifetime slots.

Open allocates one zeroed32768-byte owner arena; step advances one finite
admission phase: retained principal, actual Service token/LSA correlation,
then actual namespace opens/audit/current recheck. No child process is created.

## Actual native namespace proof

The producer opens actual `\??` and `\GLOBAL??` directory objects with NT object
manager APIs; it never constructs a `\Sessions` path. It retains both handles,
reopens their actual current names and compares kernel object identity on
every current check, audits their actual owner/DACL and brackets with genuine
principal rechecks. ACL owner must be one of the minimum trusted identities;
unrelated effective allow ACEs may query/read/traverse but may not create,
delete, set links, change DACL/owner, request maximum access or generic write/all.
Null/missing DACL, unsupported ACE type, malformed bounds or more than128 ACEs
refuse. Conservative refusal can reject otherwise benign ACL deployments.

Candidate accepts only strict `\GLOBAL??\<ASCII drive>:\...` store spelling,
with bounded4096-byte shape, no slash normalization, ADS, dot traversal or DOS
device aliases. Unicode suffix bytes are preserved as data. At most one drive
is admitted by each owner. The retained global link must target exactly
`\Device\HarddiskVolume<digits>` with no suffix, SUBST, network or reparse path.
If current and global directories differ, actual local directory enumeration
must reach documented end with no selected-drive entry; ordinary fallback
lookup cannot prove absence. Enumeration is capped at256 entries,4096 bytes
per single-entry result. A larger/unsupported directory refuses.

The native target root is actually opened using NtCreateFile with no reparse
following, read attributes and no delete sharing. FileFsDeviceInformation must
report a nonremote/nonremovable disk. FileIdInfo supplies actual volume serial
plus128-bit root file ID. Each current check reopens/compares the retained
global link, rechecks target, actual local override absence, actual retained
disk characteristics and root file identity. It never accepts caller mapping
booleans. A second drive or any failed current/candidate native observation
quarantines the canonical owner, with a sticky first diagnostic.
Volume query scratch and IOSB are zeroed before each query; successful return
also requires final IOSB status0 and Information exactly8 bytes.

The returned ordinary spelling is candidate DATA ONLY. The store must open
that candidate using its actual read-root owner and compare it with its
retained global writer using `windows_private_roots_same_directory_v2`, then
retain the actual key/hosts file owners without write/replace sharing through
the real SSH child lifetime. This leaf exposes no raw HANDLE, token, SID,
namespace object or file authority and does not change generic R2 refusal.

## Cleanup and boundedness

Native outputs are copied into canonical retained state before status checks,
including failing token, directory, link, volume, security and LSA calls.
All scratch memory is owned before native use. Any partially acquired candidate
remains in that original owner and blocks further authority. Cleanup does not
depend on current principal/namespace admission; actual canonical process and
thread are still required. It closes security allocation, LSA allocation,
handles, arena and finally principal, clearing each only after exact positive
API release. Each close turn releases at most one directly owned resource;
the final principal close has its existing finite internal cleanup bound.
`retained` or `stale` principal disposition never clears the principal owner.
Close failure keeps owner Some; a later close retries exact owned cleanup.

No Sleep, wait, background callback, subprocess, CLI, new runtime export or
unbounded polling is present. Native syscalls and bounded local enumeration
are synchronous and their real latency remains unqualified; no nonblocking
OS-call latency guarantee is claimed. The store must retain this owner until
all projections/children have finished and close their file/root capabilities
first. Invalidation refuses further path use without preventing store cleanup.

## Authored evidence and remaining qualification

Five pure production-helper cases test strict path shape, Unicode preservation,
direct fixed-volume target shape, genuine Service field correlation and
mutation-right masks. Two actual native specimens exercise real open/step,
candidate/current, second-drive quarantine, copied-alias invalidation and exact
close API completion. They require external native Win64 Service5 setup and
fail if it is missing; they contain no scripted success or platform skip.
All seven are NOT_RUN. Native fault paths, adversarial namespace/ACL changes,
same-thread scheduler behavior, import/link compatibility, syscall latency,
actual store paired-file composition, pinned SSH launch and authenticated
remote exchange remain NOT_COVERED. Source assertions are not runtime proof.

SDK contracts: [LSA session data](https://learn.microsoft.com/windows/win32/api/ntsecapi/ns-ntsecapi-security_logon_session_data),
[LSA query](https://learn.microsoft.com/windows/win32/api/ntsecapi/nf-ntsecapi-lsagetlogonsessiondata),
[directory enumeration](https://learn.microsoft.com/windows/win32/devnotes/ntquerydirectoryobject),
[kernel object identity](https://learn.microsoft.com/windows/win32/api/handleapi/nf-handleapi-compareobjecthandles).
