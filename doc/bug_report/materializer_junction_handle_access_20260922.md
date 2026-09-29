# Windows materializer junction handle access

Status: fixed; focused native API regression passes on ReFS and NTFS.

Base: `d0ef8db87adba1a6edf6d72ee8bbe197c97ab9d0`.

The receipt parent sharing fix changed `CreateDirectoryHeld` to request only
READ_ATTRIBUTES and SYNCHRONIZE. Junction creation also used that helper, so
FSCTL_SET_REPARSE_POINT received a handle without write access. The focused
regression reproduced `api.set-junction-tag:win32=5` on D: (ReFS) before the fix.
This is a handle access regression, not evidence that ReFS needs a different
link representation.

The helper now requests GENERIC_WRITE additionally only for a new junction.
Receipt parents retain read-only handles, and share=READ, exclusive creation,
ancestor protection, reparse rejection and target identity checks are unchanged.
Unix paths are unchanged; no copy fallback or symlink tag is introduced.

Validation on 2026-09-22:

- `powershell.exe -NoProfile -File scripts/check/check-materializer-junction-access-windows.ps1 -FixtureRoot D:/`: PASS on ReFS.
- Same command with `-FixtureRoot C:/Users/ormas/AppData/Local/Temp`: PASS on NTFS.
- Both cases create and validate a junction, reject a different target,
  reject a reparse target, preserve a tampered placeholder, and move a receipt
  into freshly created parents while their protective handles remain open.

The first post-fix run exposed PowerShell reflection argument wrapping in the
test's receipt-parent check; unwrapping the string argument fixed the harness.
Full Windows bootstrap was not run in this scoped change.
