# Local container request V1

Status: **AUTHORED_NOT_RUN**. This is an authored manual mirrored from
`test/01_unit/lib/common/contracts/container/local_session_v1_spec.spl`.
No compiler, test runner, doc generator, native launch or backend was executed.

The production functions accept typed local-container request metadata, encode
canonical SDN, compute SHA-256 over the exact encoded bytes, and strictly decode
those same bytes. A request or digest grants no execution, host filesystem,
container backend, network or resource authority.

| Requirement | Authored production scenarios and expected result |
|---|---|
| REQ-CARET-LOCAL-REQUEST-001: exact canonical request identity | Preserve all fields, ordered argv including empty/spaced/escaped/Unicode values, environment values containing equals, and mount permissions; re-encoding equals source; digest equals SHA-256 of those exact bytes; changing argv order or mount permissions changes digest. |
| REQ-CARET-LOCAL-REQUEST-002: bounded portable metadata | Accept POSIX and fixed-drive Windows absolute lexical paths; refuse relative paths, parent components, UNC roots, alternate data stream colons and control characters; reject normalized duplicate destinations; validate image, executable, environment, named modes, inclusive resource/dimension limits, per-text byte limits and aggregate/count limits. |
| REQ-CARET-LOCAL-REQUEST-003: strict wire input | Decode only bounded canonical SDN with the exact V1 keys and types. Reject unknown, missing, duplicated, mistyped or noncanonical fields, wrong version/kind, invalid nested mounts and argv, comments, trailing data, missing final LF and malformed syntax. |

1. Encode the fixture with distinct empty, spaced, quoted, backslash, newline and
   Unicode arguments. Decode it, compare every scalar/array/mount field, and
   compare the re-encoded bytes and exact-byte digest.
2. Alter argv order and a mount's read-only flag independently. Each digest must
   differ from the original.
3. Admit POSIX root, dotted POSIX components, drive roots and Windows separator
   spellings. Preserve authored path spelling in the payload.
4. Classify the original root before separator normalization. Apply invalid
   relative, single-backslash, Windows rooted-only, mixed-root, UNC, parent,
   ADS and control-bearing paths to cwd,
   host mount path and guest mount path; reject each before effects.
   For Windows fixed-drive paths, admit `C:/work` but refuse `C:/work.`, trailing
   spaces, DOS device components including `CON.txt`, `NUL.log`, serial/parallel
   device names and extensions, and wildcard/forbidden filename characters in
   every path role. POSIX paths retain dot/space/device-like/wildcard names.
5. Add destinations differing only by case, separators, redundant separators,
   trailing separator or current-directory components; reject duplicates.
6. Reject empty/option-like/control-bearing images, empty/NUL executable and NUL
   argv entries. Preserve empty argv entries as valid arguments.
7. Preserve `VALUE=a=b=c` and `EMPTY=`; reject malformed names, NUL values and
   case-insensitive duplicate names.
8. Admit all three networks (`host`, `private`, `none`) and both terminal modes
   (`tty`, `stdin`) at numeric endpoints. Refuse values outside CPU 1–64000,
   memory 1–1125899906842624, columns/rows 1–1000 and unknown modes.
9. Admit an argument of 16384 UTF-8 bytes; refuse 16385 bytes including a
   multibyte overflow. Independently bound image, executable, cwd, each mount
   path and environment entries. Admit exactly 1048576 canonical bytes and
   refuse the next byte plus empty/oversized decoder input.
10. Admit and decode 128 arguments, 128 environment entries and 64 mounts;
    refuse excessive counts.
11. Mutate actual encoder output to exercise strict schema, types, version,
    nested entries, semantic validation and byte-for-byte canonical equality.

Canonical encoding uses the shared canonical SDN serializer with explicit
`version: 1`, `kind: local-container-request`, camelCase field names and one
final LF. Array order is meaningful. Decoding revalidates the typed request and
requires exact equality with re-encoding.

Path identities are used only for duplicate checks: both separators fold to
`/`, ASCII case folds conservatively, empty components and POSIX
current-directory components fold away and trailing separators fold away.
Windows components ending in dot or space (including a standalone dot), DOS
device names with or without extensions, and `< > " | ? *` are refused before
identity comparison. The device-stem check conservatively trims surrounding
spaces and recognizes the superscript 1/2/3 COM/LPT spellings. These Windows
filename restrictions do not apply to POSIX components. Environment names follow
`[A-Za-z_][A-Za-z0-9_]*` with conservative ASCII case-insensitive uniqueness.
Validation preserves the original strings. It does not resolve symlinks,
reparse points, filesystem aliases, case-sensitive volume rules or host/guest
containment. Those remain the actual host owner's responsibility. The metadata
does not select a container implementation or prove that requested resource or
network policies will be enforced.

All scenarios remain unexecuted. This manual establishes authored coverage
intent only; it makes no runtime, native, performance or platform qualification
claim.
