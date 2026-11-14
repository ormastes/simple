# Administrator-installed Windows machine policy reader

Status: SOURCE_ONLY implementation in progress; NOT_RUN. This is separate from
the frozen seven-file Caret request/intent groundwork. No runtime export,
allowlist, native build, runtime test, or linker change is authorized here.

## Boundary

`windows_machine_policy_open_v1()` accepts no path, environment variable,
policy bytes, trusted SID, capacity, or provider identity. It discovers the
actual OS ProgramData location and opens the fixed existing installation
`Simple/Container/machine-policy.sdn`. It creates nothing. A private
`WindowsMachinePolicyOwnerV1` retains the exact directory chain and file.
The factory returns `Ready`, `CleanupRequired`, or a pre-allocation `Rejected`.
The owner exposes only bounded policy bytes and typed close status, never a
raw handle or caller-reconstructible root capability.

The installed-root check requires actual SYSTEM/Administrators ownership.
Current process SID ownership alone is insufficient. Relevant ancestor ACLs
must prevent untrusted replacement and security modification; creating a new
unrelated child under ProgramData is not replacement authority. The installed
directories and policy require protected DACLs that prohibit untrusted
mutation. Read access may be allowed: this policy is not a credential secret.
Unknown ACE forms, malformed descriptors and unproven ancestry refuse.

Open the exact native `\GLOBAL??\<OS-discovered-drive>:\` root through
NtCreateFile. A normal `C:\` Win32 open is insufficient: a process-local DOS
device map can select a different administrator-owned backup with preserved
ACLs. The explicit global namespace avoids that local-first lookup. Query the
retained root's FileFsDeviceInformation and require disk type with no remote
device flag; GetFileType alone does not establish local storage. Resolve each remaining
component relative to its retained parent, requesting no reparse traversal and
checking actual handle metadata. Retain ancestry without delete sharing and
the file without write/delete sharing. Do not reopen by a composed pathname.
Drive-rooted UTF16 paths are bounded; unsupported remote/device paths refuse
rather than changing the authority boundary. Later state and ledger bridges
must retain this global provenance and must never reopen through a normal DOS
path. No query-target-then-normal-path fallback is allowed.

## Lifetime

The existing native-thread guard serializes a private generation registry.
Opaque owner copies refer to the same canonical slot; they cannot close a
resource twice or recover a closed generation. Every allocation and returned
handle is recorded before checking success. Failed LocalFree, CloseHandle or
HeapFree preserves the exact cleanup obligation. Known-folder output is freed
with CoTaskMemFree even when discovery fails. A read checks the retained
owner's liveness/security and preserves the same bounded file identity.

`Ready` means actual installed-policy read provenance. It does not mean an
authenticated local principal, provider observation, native attach receipt,
capacity reservation or delegation exists. The subsequent local service
factory must decode these actual bytes, bind the machine/provider observation,
and acquire the shared physical-capacity writer before admitting execution.
No public metadata decoder can mint this native owner.

## Reuse and missing integration

Reuse existing kernel32 handle/heap calls and the descriptor/ACL SFFI family
already used by `windows_engine_pipe_native_v1`. Only narrow native OS calls
for OS folder discovery and relative opens are added; no `rt_*` symbol or C
registry operation is added. The existing Windows private-root predicate
accepts the current SID and therefore does not establish this installed
machine-root provenance.

The existing `host_primary_service_command_v5` and
`smux_server_serve_runtime_domain_v5` remain the credential/listener and native
owner composition. The future local-domain arm must carry this actual reader
and an actual shared reservation owner. Reusing a transport or adding a union
tag alone does not supply machine authority. No new daemon or silent elevation
is introduced. Host enrollment and local admission still need the shared
physical-scope selector and accounting consumer.

## Native qualification obligations

The all-source Windows linker lists shell32, ole32 and ntdll; ordinary MSVC and
some entry-closure link routes currently omit shell32/ole32. Therefore source
authorship does not establish linkability. SHGetKnownFolderPath requires
shell32, CoTaskMemFree requires ole32, and NtCreateFile requires ntdll. No
linker defaults are changed by this lane.

Native fixtures must use an administrator-installed canonical policy. The
tests do not rewrite policy, change ACLs or install a service. Reparse, foreign
owner, broad write ACL, discovery failure, partial allocation and failed close
cases require explicit isolated native fixtures/fault injection; authored
manual procedures are not executed coverage. No Linux result certifies this
Windows owner.

An isolated local-drive-shadowing fixture must demonstrate that a local `C:`
mapping to an administrator-owned backup cannot select policy. This remains
MANUAL_NOT_RUN; no drive map is modified by the authored ordinary fixture.

The OS contracts used are [SHGetKnownFolderPath](https://learn.microsoft.com/en-us/windows/win32/api/shlobj_core/nf-shlobj_core-shgetknownfolderpath),
[known folder identifiers](https://learn.microsoft.com/en-us/windows/win32/shell/knownfolderid),
and [NtCreateFile](https://learn.microsoft.com/en-us/windows/win32/api/winternl/nf-winternl-ntcreatefile).
The namespace distinction is documented in
[local and global DOS device names](https://learn.microsoft.com/en-us/windows-hardware/drivers/kernel/local-and-global-ms-dos-device-names);
the local-disk predicate uses
[FileFsDeviceInformation](https://learn.microsoft.com/en-us/openspecs/windows_protocols/ms-fscc/616b66d5-b335-4e1c-8f87-b4a55e8d3e4a).
