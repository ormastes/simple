# Windows checked source reads return invalid optional text on failure

Observed under pure-Simple Phase2 producer8469: SCV rejected an event for
`test/fixtures/compiled_tool_protocol/protocol café.spl`, a297-byte fixture,
with byte_count=-1. All five digest facets and the source identity validated.
The negative count existed before transient promotion.

The actual C checked reader called narrow CRT open on UTF-8 path bytes and
returned0 on failure. Its `text?` contract uses canonical nil3. Actual caller
disassembly compared against3, retained0 as present, and computed string length
-1. The Rust checked-reader twin already returns canonical nil.

Repair: the native checked reader uses the existing UTF-8/UTF-16 fd owner on
Windows and returns canonical nil for every explicit failure. Binary I/O,
offset/cap validation, cap-clamping and managed empty successes are preserved.
SCV now refuses a failed read and ends its owned scratch scope rather than
manufacturing empty source content with `?? ""`.

Focused native regression:17 checks passed, exit0, empty stderr, including
the actual Unicode fixture compared byte-for-byte with independent Windows
wide-file reference I/O, ASCII, offsets/caps, empty and EOF, embedded NUL/^Z/
CRLF/UTF-8, missing files, invalid arguments and invalid UTF-8 paths. Against
the original runtime archive, the same harness exits5 on the Unicode fixture.
Allocation/read syscall fault injection was not performed; their failure
branches are reviewed to return canonical nil. Existing string allocation
failure already returns canonical nil through rt_string_new.

New executable SSpec cases cover failed-read scope cleanup and real empty
source admission. These SSpec cases remain unexecuted until a qualified native
test runner is available. Runtime-only manual Phase2 relink does not include
the new SCV source guard; Phase3 must incorporate and qualify that SPL change.

Evidence: phase3-validation-20261016/core-checked-reader-repair-cycle1.
Bug database reconciliation remains pending; this dated record preserves the
concrete evidence while its qualified database tool is unavailable.

## Fresh native counterfactual, 2026-10-18

The actual `0405` producer (source cohort `b790`) reproduced the same defect:
its Git owner emitted event 36967 for `protocol café.spl` with byte_count=-1
while all five digest facets were valid. This evidence identifies a stale
producer lacking existing fix `c1f630e7a05`, rather than a new SCV validator bug.

The existing `test/04_smoke/core_checked_reader_native.c` was linked twice
against the same retained original `0405` core-C runtime archive. Baseline
exited 5 at the actual 297-byte Unicode fixture. The counterfactual compiled
the original `b790` `runtime_native.c` with only the exact existing checked-reader
hunk from `c1f630e7a05`, then supplied that object before the unchanged archive.
It exited 0 with empty stderr and:

```text
CORE_CHECKED_READER_PASS checks=17 unicode_fixture_bytes=297
```

The fresh executed assertion count is **17**. The original evidence paragraph
above remains historical; this run independently confirms the same count.
The fixed link map binds `rt_file_read_text_at_checked`, `rt_open_fd`, and
`rt_string_new` to `runtime_native_fixed.obj`. Normal strict linking used
`/OPT:REF`, without undefined-symbol substitutes or permissive link flags.
Compilation used LLVM `clang-cl`, the MSVC ABI and `/MT`, MSVC headers
14.44.35207, and Windows SDK 10.0.26100.0.

Retained local evidence: `C:/dev/p4-reader/receipt.json`, with native stdout,
baseline/fixed exit status, exact source diff, compile/link response files,
maps, source/tool/archive/executable hashes, and a conservative 17-header local
include closure. Fixed executable SHA-256:
`476d8fcfc5fc1027618b12c6a9820c7e5a7e4c7c0e9df4514b3a248426a528fc`.
The original archive was reused without mutation. No green native check was
rerun. This native-only result does not qualify the separate SPL failed-read
guard, complete SCV refresh, bootstrap phase, or full CLI; those remain owned
by the subsequent producer build and its admission checks.
