# Windows legacy file sync opens a read-only handle

Status: native regression passed; canonical database registration pending via its API.

Five library builds on source a69376d4605 reached no HIR artifacts. Two reported
`SCV-E-ADMISSION: snapshot-inventory-write-failed`; three timed out behind inventory
refresh. A warm traits diagnostic completed authenticated inventory generation 2,
then failed snapshot writing after 17,459 materializations and 52,377 verifications
(174.9 seconds). Inventory publication was not full snapshot admission.

A small C diagnostic linked the exact retained compiler archive and runtime owner
objects, replacing only its startup main. It called the real compiled
`lib__scv__store__scv_write_text` with runtime-created text values. Both an 18-byte
LF payload and the 8,235,828-byte real inventory payload returned false. Its direct
production `rt_file_sync` control returned zero, errno 9 and Windows error 5
(access denied). No snapshot inventory output was produced. Diagnostic source:
`C:/dev/generic-hardening-atomic-write-probe-20261030.c`, SHA256
`EDB30662E88249632FB391A64FD59868864828D73F56AE2FC5EB335B37EE4D05`.

`runtime_legacy_core.c` opened the existing file with `rb`, then called `_commit`.
Windows flushing requires a writable handle. Use `r+b` on Windows: it opens an
existing file without creating, truncating or rewriting it. POSIX `rb` plus
`fsync` remains unchanged. The other runtime.c and secure-staging owners already
request writable Windows handles; no changes are needed there.

The native selfcheck exercises real sync on empty, small and inventory-sized
binary files, verifies every byte and EOF afterward, and rejects missing,
read-only and directory paths. This checks actual OS flush return status; it does
not claim simulated power-loss durability. The compiled SCV diagnostic must also
pass and match its exact payload before declaring the snapshot blocker repaired.
Only the legacy-core owner needs recompilation; retain the compiler archive,
other runtime objects and prior evidence.

Validation on 2026-10-30 replaced only that owner using a byte-preserving b81
overlay of this exact sync hunk (SHA256
`69E0056233916F62F353A7B0AC5445E66140F7EA6944045D1C69990D9F6EEEDD`).
The retained compiled SCV writer then succeeded on both 18-byte and 8,235,828-byte
payloads; each output matched the input byte for byte. The native selfcheck also
passed its empty/small/large preservation and negative cases. The tested
selfcheck SHA256 was
`60BBC05D1A84282D3B792F32C8FD963058C7B41C1B8F75FE16EDF60DBF7192DB`.
These are runtime-owner results, not a claim that the five compiler libraries or
Phase 3 have completed.

Future standalone regression command: `CC=<Windows-GNU-clang> sh
scripts/check/check-windows-file-sync.shs` on Windows. This checker builds eight
real runtime owners for independent qualification. The current incremental
diagnostic instead replaces only the retained legacy-core object; do not confuse
that narrower execution with having run the standalone checker.
