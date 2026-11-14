# SCV source manifest membership rejects non-ASCII paths

**Bug ID:** `source_manifest_membership_unicode_byte_slice_2026_11_14`  
**Status:** fixing  
**Severity:** P2

## Symptom

SCV snapshot admission can reject a valid selected-source manifest when the
selected rows contain a non-ASCII path. The failure is reported as
`snapshot-source-membership-mismatch`.

## Cause

`index_of("|")` returns a UTF-8 byte offset. The ordered membership helper
used that offset with bracket slicing (`row[0:separator]`), which counts
Unicode code points. With `test/fixtures/compiled_tool_protocol/protocol café.spl`,
the extracted identity includes the pipe. The ordered check still accepts the
batch, then the merge advances past the actual inventory entry and rejects
the exact row. The pinned admitted P2 source and current release source had
the same implementation.

## Evidence

The bounded native import attempt using broad `--source test/fixtures` exited
before producing an executable with `SCV-E-ADMISSION:
snapshot-source-membership-mismatch`. The captured manifest had 14,550 rows;
the selected inventory had 46,141 entries. All rows matched in an independent
byte-oriented comparison. The manifest contained two non-ASCII identities;
simulating the source helper's byte-offset/code-point-slice path reproduced
the first false-negative at row 12,209. This is source-bound reproduction of
the helper logic and a real admission failure, not a standalone native helper
test.

## Fix and verification

Use byte-oriented `substring(0, separator)` at each separator-derived identity
extraction, and retain a regression that selects more than 32 rows so it
exercises the ordered merge path with a non-ASCII identity. Direct helper
runtime verification and the changed-scope native import remain to be recorded.

