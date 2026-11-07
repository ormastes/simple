# Windows private journal capability V1

The typed owner is `std.nogc_sync_mut.io.windows_private_file_v1`. The native Windows boundary is
`src/runtime/platform/runtime_windows_private_root.h`. There is no second
process registry or journal authority. The narrow native IO registry has 256
slots, at most 64 pinned ancestry components per root, and non-reused monotonic
generations. Simple values contain only tokens;
all validation, IO, close, publication, cursor/quota accounting and authoritative
write/sealed/published transitions occur under one exclusive native owner lock.
Copied stale values cannot dereference freed memory, close a recycled HANDLE,
or write through a copy made before sealing. Exhaustion fails before OS effects.

`windows_private_root_open_v1` admits an installed local fixed-volume absolute
DOS path. It normalizes forward slashes, rejects UNC/device paths and substituted
drive roots, walks each component relative to its pinned parent with
`NtCreateFile`, and opens every component without reparse traversal. Ancestor
handles remain pinned without share-delete or share-write. Ancestors reject
foreign mutation; the final journal root additionally requires a protected
DACL rejecting foreign read/execute/metadata access. The trusted set is the
current process user, LocalSystem and built-in Administrators. Impersonation is
rejected. Unknown ACE forms fail closed. Owner trust is checked independently
because ownership grants implicit security-descriptor control.

This deliberately requires an installer-controlled ancestry. Stock `C:\` ACLs
that grant Users folder creation may fail admission. The implementation never
repairs deployment ACLs or uses POSIX mode as Windows privacy evidence.

`child_directory(name, create)` opens an existing child or exclusively creates
one with a protected process-user DACL attached at creation. It duplicates the
pinned ancestry so child cleanup is independent of parent cleanup.
`create_private_stage(name, maximum)` returns an exclusive regular-file owner;
`write` appends bounded chunks of at most 1 MiB with an enforced cumulative
maximum of 8 MiB. `seal` flushes the exact file, refreshes identity metadata and
disables further writes through the facade. `read_all_bounded` reads at most
8 MiB in 1 MiB chunks and validates identity and privacy. Reparse points,
multiple hard links, unprotected DACLs and foreign rights fail admission.

`publish_no_replace(stage, name)` renames the retained sealed handle relative
to the retained directory. `Ok(true)` means publication succeeded and the
retained final handle still passes privacy checks. `Ok(false)` means a name
collision; bytes have not been compared. The caller must open the colliding
file with `open_private_file`, check its privacy and compare its complete
bounded bytes before acknowledgment. Publication never replaces that entry.
The stage remains caller-owned on every outcome. The caller closes the retained
published handle before attempting another exclusive open of its final name.
The documented relative rename contract is supported by
[Microsoft FILE_RENAME_INFO](https://learn.microsoft.com/en-us/windows/win32/api/winbase/ns-winbase-file_rename_info).

Admission failures use `WindowsPrivateErrorV1(message, cleanup_root,
cleanup_file)`. Any returned cleanup owner must remain reachable until close
succeeds. A failed close preserves the exact handle or remaining ancestry
chain; it never fabricates a closed state. Native root admission returns a
non-ready cleanup lease if attempted cleanup fails. The root-ready query
revalidates all retained ancestry before further operations. There is no
background retry. Failed token `CloseHandle` and security-descriptor `LocalFree`
operations remain attached to the exact IO generation and block further use
until explicit cleanup succeeds. UTF16 and byte-buffer temporaries use bounded
`malloc` allocations with infallible `free`, avoiding unchecked `HeapFree`.
Publication refreshes identity on the authoritative registry record after a
successful rename, so the exact retained final handle supports readback.
The successful kernel rename consumes publication immediately under the native
owner lock. A subsequent security or snapshot failure makes the owner cleanup
only; no copy can rename the published receipt again after that error.

## Verification status and required host evidence

Native Windows execution: **NOT_RUN**. No Windows fixture or approved build was
available in this task. Source changes are not deployment qualification. The
Rust bootstrap seed does not provide these symbols; it is not a supported
producer or a fallback for this capability.

`test/02_integration/lib/windows_private_file_v1_spec.spl` requires fresh
installer-owned empty/private, foreign-read-ACL and reparse-root fixtures via
`SIMPLE_WINDOWS_PRIVATE_EMPTY_ROOT`,
`SIMPLE_WINDOWS_PRIVATE_FOREIGN_READ_ROOT`, and
`SIMPLE_WINDOWS_PRIVATE_REPARSE_ROOT`. Missing fixtures fail explicitly. It
checks actual publication, retained readback, privacy checks, collision
preservation, copied-before-seal write rejection, and stale copied root/file
rejection after slot reuse. Additional qualification must inject failed `CloseHandle`, deny
generic read/write/delete/security-control rights, test owner mismatch and
unprotected DACLs on root/stage/collision, race ancestry replacement, exercise
8 MiB chunked IO, and independently attempt access as an untrusted principal.
`src/runtime/test/rt_windows_private_post_rename_selfcheck.c` provides a
test-only failed-security-query wrapper after a real successful kernel rename.
It checks that a retry cannot move the published entry. The production provider
has no injected-success or fault bypass. This authored native regression is
also **NOT_RUN** until a Windows fixture and build are available.

The supported durability profile is **process crash**, with an observed
successful `FlushFileBuffers` on the exact file before publication. Durable
directory entry persistence across power loss is **unsupported**. A caller
requesting that stronger profile must reject admission rather than infer
support from the file flush result.
