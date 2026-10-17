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
