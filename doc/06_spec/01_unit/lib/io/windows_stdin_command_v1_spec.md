# Pinned bounded Windows stdin command contracts

Status: **AUTHORED_NOT_RUN**. Nine authored production-helper cases; no test
runner, Windows native execution, compiler, build or mapping campaign ran.

Source: `test/01_unit/lib/io/windows_stdin_command_v1_spec.spl`.

REQ-WINDOWS-STDIN-001: explicit Windows paths and lowercase SHA256 identity,
bounded binary input, independent output bounds and exact argv are mandatory.

REQ-WINDOWS-STDIN-002: a completed local stdin prefix is distinguished from a
queued operation; unknown/pending IO retains its backing storage.

REQ-WINDOWS-STDIN-003: image and cwd ancestor paths are retained by the native
pin; pure path enumeration does not prove those handles were acquired.

| Production contract | Expected behavior |
|---|---|
| Caller mutation after the production freeze helper | Independent argv, environment and binary input |
| OS native volume spelling, full SUBST suffix chain and file-ID comparison | Stable native paths; exact volume/128-bit ID match required; mutable DOS/remote anchors refused |
| Gateway frame at 2 MiB + 8192 header + 16 prefix | Admit 2105360 bytes; reject larger input |
| Relative/UNC/device/ADS/dot/reserved path forms | Reject before native effects |
| Missing, uppercase or malformed executable SHA256 | Reject |
| Known partial/full completed stdin prefix | Advance only the actual completed count; reject impossible ranges |
| Pending, invalid-handle and unknown IO errors | Retain overlapped storage |
| Program/cwd ancestor enumeration | Retain each volume/root parent once |
| Binary stdin with fixed typed argv | Preserve argv without interpolating stdin |

These cases exercise actual production helpers, not mock process results.
They do not establish native pinning, named-pipe pairing, process reaping,
credential ACLs, EOF, cancellation, cleanup or remote effects.
The freeze case calls the same helper wired into `begin`; it does not execute
Windows `begin` or a native process. Constructed path/file-ID values likewise
test reducers, not actual OS resolution or native image selection.
