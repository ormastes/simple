# Windows SHA256 file hashing rejects long cache paths

Date: 2026-10-18. Bug database reconciliation pending: no qualified database
tool is available in this repair lane.

Producer `2fa6f60b50f7e82bfc5f0dbf7c8ea3910b25fac595cf0f0195cbce1dae1e72d5`
compiled Hello but failed its cold native capsule publication gate. The retained
631-byte AMD64 object has SHA256
`6371b7312479cf686061939f267f4f695a43a80a3e03c03fdbd36e9582df6550`.
Its six-line receipt has size 631 and an empty digest field. Its object path is
262 characters; extended-path reads preserve the actual bytes and receipt.

The real runtime hash owner `rt_sha256_file_raw_v1` used narrow `fopen`.
An authorized read-only `ucrtbase.dll` control failed to open the 262 character
forward/backslash paths (errno 2), while extended-path and 173 character copies
opened and hashed to the same expected digest. This dynamic CRT control is
analogous evidence, not execution of the producer's static CRT hash function.
The separate Simple fingerprint nil/text admission issue is owned independently.

The fix uses the existing Windows UTF-8/extended-path helper and `_wfopen`,
frees its temporary wide path, and preserves fail-closed open/read behavior.
Non-Windows file opening and the SHA algorithm remain unchanged.

The dedicated Windows C self-check calls exported `rt_file_hash_sha256` from
genuine core-C translation units. It checks short and >260 character Unicode
paths containing identical binary bytes, empty files, and missing files.
No hash/FFI implementations are supplied by the test. Invalid UTF-8 paths must
also return nil.

The actual static-CRT counterfactual passed on 2026-10-18: all 40 genuine C
translation units compiled with `/MT`; the baseline linked against the exact
`2bcc8144b1bf4b16af66d6c0a5c9bd76e1c3ac8f` runtime TU and exited 1 with exactly
the two expected long existing-file hash failures. The fixed TU exited 0 with
the exact PASS line and empty stderr. Both maps identified the intended real
runtime hash providers. The shared 37 runtime objects, test, headers and tool
flags were identical between links. Existing successful compilation and the
baseline link were preserved when an exact-symbol map observer was corrected.

Fixed self-check executable SHA256:
`458c0ac6aaadb93a43f3bc165246e9a0837a2eb6bd93da1981c522d97a35febf`.
This qualifies the Windows C hash fix, not the Simple compiler or the full C
tree. Broader core checks remain UNRUN; no producer relink or new Hello run was
performed. The two existing Windows runtime scripts exercise other operations
with extracted helpers; neither currently runs this dedicated full-runtime
hash self-check. The retained compile plan and raw receipts provide the current
manual execution evidence.

Local diagnostic artifacts are under
`C:/dev/simple-bootstrap-storage/scope-producer-3d9d-20261018/phase2-ee3-mir-owner-repair-PENDING/qualification/hello-attempt3-retention-FINAL/retained-manual-proof/`.

Native counterfactual receipts, compiler arguments, maps and raw streams are in
`C:/dev/simple-bootstrap-storage/scope-producer-3d9d-20261018/windows-sha256-long-path-selfcheck-PENDING/`.
