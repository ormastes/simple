<!-- codex-research -->

# Workspace Root Write Guard - Domain Research

## Filesystem Semantics

On Unix-like systems, creating or deleting entries in a directory is controlled
by write permission on the containing directory, with execute/search permission
needed to traverse it. Removing write permission from a directory prevents
normal users from creating new files or subdirectories there, but privileged
users can still override it.

On Windows, directory creation rights are represented through ACL entries.
Microsoft documents `icacls` as the command-line tool for displaying and
modifying discretionary access control lists. Windows file access constants
distinguish directory rights such as creating a file in a directory and creating
a subdirectory. .NET exposes the same concept through `FileSystemRights`, where
`Write` includes creating folders and files.

Sources:

- Microsoft Learn: `icacls`
  https://learn.microsoft.com/en-us/windows-server/administration/windows-commands/icacls
- Microsoft Learn: File access rights constants
  https://learn.microsoft.com/windows/desktop/FileIO/file-access-rights-constants
- Microsoft Learn: `System.Security.AccessControl.FileSystemRights`
  https://learn.microsoft.com/en-us/dotnet/api/system.security.accesscontrol.filesystemrights
- OpenBSD `chmod(1)` manual
  https://man.openbsd.org/chmod.1

## Unix/macOS Strategy

Use owner/group permissions or ACLs:

- Audit mode: no elevated privileges required.
- Fix mode: move misplaced files into an allowed quarantine path.
- Lock mode: use `chmod a-w <dir>` or ACLs on selected directories.
- Unlock mode: restore write permission from a saved manifest.

`sudo` should only be needed if the script changes ownership or permissions for
paths not owned by the current user. A safer design is to keep the repository
owned by the developer and request elevation only for the lock/unlock backend.

## Windows Strategy

Use NTFS ACLs:

- `icacls <dir> /deny <user>:(WD,AD)` can deny file creation and subdirectory
  creation rights, but deny ACEs are sharp tools and can surprise inherited
  permissions.
- A safer lock backend should save existing ACLs first with `icacls /save`,
  apply narrow denies only to protected directories, and provide an unlock
  command that restores the saved ACLs.
- Running as Administrator is the Windows equivalent of using elevated
  privilege for ACL changes. The audit/fix workflow should not require admin.

The Windows implementation should prefer PowerShell/ACL APIs or `icacls` with a
dry-run preview. It should not rely on Unix `chmod`, which has different
semantics on Windows.

## Practical Design Pattern

Do not make the whole repository immutable. Use a policy-driven allowlist:

- Root: allow only entries declared in `FILE.md`.
- Immediate root children: either allow declared subpaths or enforce only
  directory-level cleanliness for selected children.
- Mutable dirs: keep build/cache/temp paths writable.
- Tool writes: MCP/editor/agent writes should be intercepted or redirected when
  possible, but shell/build writes need filesystem permissions or post-write
  audit.

## Conclusion

The achievable path is a two-stage guard: first a deterministic audit/fix script
that reads `FILE.md`, then optional platform-specific permission lock/unlock
backends. Windows support requires ACLs via `icacls` or PowerShell, not `sudo`.
