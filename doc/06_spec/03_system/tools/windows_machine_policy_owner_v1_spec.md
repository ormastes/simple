# Actual Windows machine installed-policy owner V1

Status: **AUTHORED_NOT_RUN**. Authored manual mirrored from
`test/03_system/tools/windows_machine_policy_owner_v1_spec.spl`.
No builds, tests, native execution, generated-doc run or Windows qualification
was performed. Unsafe-source review and exact linker-route admission remain
required before execution.

The fixed factory discovers ProgramData using `SHGetKnownFolderPath` and
`FOLDERID_ProgramData`, then opens the existing
`Simple\Container\machine-policy.sdn` installation. It accepts no caller path,
environment override or claimed ACL boolean. It reads real nonempty bounded
bytes before returning Ready. This establishes installed-file provenance only;
it does not parse policy, reserve resources or grant machine capacity authority.

| Requirement | Actual authored native scenario |
|---|---|
| REQ-WINDOWS-MACHINE-POLICY-001: installed-file provenance | Call the real fixed factory on an actual protected Windows installation, without path input or self-installing a fixture. Missing installation and unsupported hosts explicitly fail. |
| REQ-WINDOWS-MACHINE-POLICY-002: same retained bytes | Read the actual retained file twice. Each read rechecks ancestry/file metadata and ACLs, seeks offset zero and returns nonempty bytes bounded to one MiB; compare byte arrays exactly. |
| REQ-WINDOWS-MACHINE-POLICY-003: canonical cleanup identity | Close the actual owner, then reject reads through its copied wrapper and return stale for repeated closes. |

1. **Open the actual administrator-installed machine policy.** An administrator
   must independently prepare the fixed installation in the actual ProgramData
   location. Every ancestor has SYSTEM/Administrators ownership and refuses
   untrusted mutation of existing ancestry. Installed `Simple`, `Container` and
   the policy file have protected present DACLs with no untrusted mutation
   rights. The policy is an existing regular non-reparse file with one hard
   link, nonempty contents and at most 1048576 bytes. The spec does not create,
   modify, repair or install it.
2. **Read the same retained policy bytes twice.** Use the returned owner only.
   Compare complete byte arrays, require nonempty contents and enforce the
   size bound. No pathname reopen or policy-content substitution is involved.
3. **Close and reject a copied owner.** Copy only the actual returned wrapper,
   close through production cleanup, then require copied reads to fail and
   copied/original repeated closes to report `stale`.

Fixture owners remain retained in the spec's actual-owner list if assertions
or native cleanup fail. Read results are collected without unwrapping, and
cleanup is attempted before result assertions can abort. A CleanupRequired
factory result is retained for diagnosis, attempts one actual close and fails
fixture opening; it is never turned into a fabricated successful owner.

The root uses counted native `\GLOBAL??\<OS-discovered-drive>:\` with
`NtCreateFile`, RootDirectory zero, FILE_OPEN, SYNCHRONOUS_IO_NONALERT,
DIRECTORY_FILE and OPEN_REPARSE_POINT. It does not open through a process-local
DOS drive map, query a link target and reopen, or use a normal Win32 drive path.
The retained root's FileFsDeviceInformation query requires DeviceType DISK (7)
and rejects FILE_REMOTE_DEVICE (0x10), with exact native/IOSB success and eight
returned bytes. GetFileType DISK alone would also admit remote files. This is
a machine-global local-disk predicate, not proof of fixed/nonremovable physical
hardware or capacity. Each remaining component is a single relative
`NtCreateFile` child under a retained
directory handle, with OBJ_CASE_INSENSITIVE and OPEN_REPARSE_POINT. Exact
handle metadata rejects reparse points and wrong types. No unsupported
object-namespace flag is treated as a filesystem guarantee. Directories deny
delete sharing; the policy permits read sharing only. The native UTF16 known
folder path remains UTF16 throughout discovery and walking.

Ancestors may allow ordinary principals to create children, while rejecting
write attributes, write EA, delete-child, delete, owner/DACL mutation and
generic write/all. Installed directories/file additionally reject data/append
rights and require protected DACLs. SYSTEM and Administrators are the only
trusted owner/trustee classes; current-user SIDs do not become trusted. Unknown
ACE forms fail closed. The factory and each read refuse thread impersonation.
Public owner fields and named construction remain module-private; public
methods use authoritative same-thread generation/closed registry state.

The following require independently prepared isolated Windows snapshots and
remain **MANUAL_NOT_RUN**, with no claimed executable coverage:

- Missing installation: observe explicit refusal on an image with no installed
  policy; do not remove or mutate a live installation for this test.
- Unsafe ancestry, reparse components, wrong owner, unprotected/mutable DACL,
  unsupported ACE forms, hardlinks, oversized/empty policy and impersonation:
  use separately prepared administrator-controlled images and observe refusal.
- Partial native failures and failed `LocalFree`, `CloseHandle` or `HeapFree`:
  require actual fault hooks/receipts; no hooks currently exist in this spec.
  Ownership must remain CleanupRequired or `retained`, and a later confirmed
  release must retire the same native resources without double-free.
- Cross-thread use and capacity exhaustion: require actual isolated owner
  threads/resources; source review does not establish observed behavior.
- Local DOS drive shadowing: use an independently prepared disposable Windows
  snapshot with a local drive map selecting an administrator-owned backup and
  distinct policy bytes. Confirm the actual factory still reads the global
  installation or refuses; the ordinary fixture does not create an attack map.
  A later state/ledger bridge must keep the same global/handle-relative root
  provenance and must never reopen a normal DOS path.
- A global drive selecting a remote filesystem or a non-DISK device must
  refuse using actual retained-handle volume metadata. This procedure requires
  a separately prepared snapshot; no synthetic metadata is accepted.

Native link requirements are shell32 (`SHGetKnownFolderPath`), ole32
(`CoTaskMemFree`), ntdll (`NtCreateFile`, `NtQueryVolumeInformationFile`), advapi32 (`OpenThreadToken` and ACL
inspection), kernel32 (handle, heap, file and thread operations) and the existing
owner-thread guard. Ordinary native-link/MSVC default lists currently omit
shell32/ole32; all-source lists containing them do not qualify a different
closure. Exact linked imports and live Windows behavior remain unverified.

SDK references: [known-folder allocation contract](https://learn.microsoft.com/windows/win32/api/shlobj_core/nf-shlobj_core-shgetknownfolderpath),
[native relative file API](https://learn.microsoft.com/windows/win32/api/winternl/nf-winternl-ntcreatefile),
[retained-file metadata layout](https://learn.microsoft.com/windows/win32/api/winbase/ns-winbase-file_standard_info),
[volume query ABI](https://learn.microsoft.com/windows-hardware/drivers/ddi/ntifs/nf-ntifs-ntqueryvolumeinformationfile),
[local-disk device predicate](https://learn.microsoft.com/openspecs/windows_protocols/ms-fscc/616b66d5-b335-4e1c-8f87-b4a55e8d3e4a).
