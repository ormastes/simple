# Checked column engine fixtures

Authored acceptance manual, 2026-10-03. No fixture has been executed in this
session; these files are inputs to the existing differential harness, not
evidence of engine parity or a completed REQ-001.

The paired fixtures are
`test/fixtures/engine_differential/collection_req001_checked_columns_sync.spl`
and `collection_req001_checked_columns_async.spl` in the same directory.
Each imports its corresponding production dataframe facade and shares the
same behavioral oracle. Both have an exact sibling `.spl.expected` marker.

| Production behavior | Independent oracle before success output |
|---|---|
| Checked integer roundtrip | Three rows; present values 11 and 33; mask false/true/false; checked missing lookup is absent. |
| Checked float roundtrip | Present values -1.25 and 3.5; mask false/true/false. |
| Index rejection | -1 and 3 produce exact IndexOutOfBounds payloads for length 3. |
| Dtype rejection | Float dynamic storage passed to integer adapter reports expected I64, declared F64, backing F64. |
| Mask rejection | One value with an empty mask reports MaskLength(1, 0). |
| Reversed view | Offset 2 and stride -1 yield 33,22,11. |
| Strided view | Length 2 and stride 2 yield 11,33. |
| Invalid extent | Length 3 and stride 2 reject with stride-outside-backing. |

Every branch mismatch returns a nonzero exit code. Success prints one fixed
marker only after all checks; masked payload contents are intentionally not
asserted because missingness defines the semantic value. No adapter logic is
reimplemented in these fixtures.

Once an admitted self-hosted runtime exists, select these fixtures with
`DIFF_FILTER=collection_req001_checked_columns` and require `DIFF_CERTIFY=1`
in `scripts/check/check_engine_differential.spl`. Strict certification requires
every requested distinct engine, zero build/run exits and exact oracle output.
JIT remains uncertifiable without its runtime-owned execution witness. The
async storage family fixture tests its facade semantics, not async scheduling.
IEEE special values, other scalar types, serialization and measured NFRs remain
separate acceptance obligations.
