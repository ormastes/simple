# Existing private-root global namespace compatibility

**AUTHORED_NOT_RUN.** Three executable scenarios are authored in
`test/03_system/tools/windows_private_global_root_v1_spec.spl`; no native,
build, interpreter, compiler or docgen execution was performed.

The existing root-open exports accept one additional exact spelling:
`\GLOBAL??\C:\<one-or-more-child-components>`. The prefix is case-sensitive;
the drive is an ASCII letter. Existing component/depth bounds and rejection
of traversal, ADS, repeated/trailing separators and trailing dots/spaces apply.
The global branch also rejects malformed UTF16 surrogate sequences. Unicode
components remain supported. Ordinary drive-letter callers keep their existing
root-open semantics.

An administrator must independently provide:

- `SIMPLE_WINDOWS_PRIVATE_GLOBAL_ROOT_FIXTURE`: an ordinary absolute drive path
  to an existing private protected directory on the machine-global drive.
- `SIMPLE_WINDOWS_PRIVATE_GLOBAL_UNICODE_FIXTURE`: another actual protected
  directory whose path contains `機器`.

The fixtures do not create directories, install policy, alter ACLs or modify
drive mappings. Unsupported hosts and missing fixtures fail explicitly.
Returned native owners are retained for diagnosis and closed before assertions.
These are generic private-root fixtures; their success does not establish
machine-policy authority, enrollment, capacity or a local service domain.

| Scenario | Actual authored assertion |
|---|---|
| Ordinary/global compatibility | Both factory calls return actual roots with current native security; both are closed before checking results. |
| Unicode preservation | The actual global fixture path retains its Unicode component and opens successfully. |
| Invalid global spelling | The Windows production factory refuses wrong-case prefixes, absent child, relative drive, traversal, ADS and malformed separators. |

The global branch opens the native absolute global drive root through
NtCreateFile. It does not call local-DOS GetDriveTypeW/CreateFileW, query a
target and then reopen it, or change the process device map. It checks the
actual retained root's volume information for disk type and absence of the
remote-device flag, then applies the existing kind, ACL and GUID-volume-root
checks. Subsequent child opens remain handle-relative. Any native output handle
is retained before checking status; a failed close preserves cleanup ownership.

Separate isolated snapshots/fault hooks are required for the following
**MANUAL_NOT_RUN** procedures; no executed coverage is claimed:

- Shadow a local drive mapping onto an administrator-owned backup with preserved
  ACLs and different sentinel data. Verify that the explicit global path still
  selects the machine-global fixture, while ordinary behavior stays unchanged.
- Supply remote/non-disk volume, reparse, foreign owner, unprotected ACL and
  mutation-permitting fixtures; observe the appropriate refusal.
- Force native open/query/close failures, including uncertain handle output,
  and verify that the exact returned cleanup owner remains retryable.

No new exported runtime symbol is added. Existing journal export admission,
native linkage and Windows qualification remain separate pending gates.
