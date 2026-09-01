# Query Check Output Line Cursor Specification

Source: `test/01_unit/app/cli/query_check_output_line_cursor_spec.spl`

Evidence status: authored but not executed under the user-requested no-verify
override.

## Scenario: line admission and order remain exact

The executable fixture combines leading/trailing empty lines, CRLF, a banner,
Unicode messages, and duplicate diagnostics. Collection must preserve the exact
three JSON objects in order, while the count owner returns the same cardinality.
Empty, newline-only, and unrelated-file output remain empty.

## Scenario: each line is consumed by a bounded byte cursor

The structural fixture bounds both count and collection owners, requires their
shared newline finder, terminal break, and monotonic `line_end + 1` progress, and
rejects whole-output `split` arrays. The helper itself must compare newline bytes
without substring construction.

For S output bytes, maximum physical line length M, prefix bytes P, diagnostic
output bytes D, and K diagnostic handles, each owner performs O(S) traversal.
Counting retains O(M + P) auxiliary text; collection retains O(M + P + D + K).
This replaces an O(S) line-array/slice retention interval but is not a zero-copy
parser and does not fuse count with collection. No
runtime allocation, timing, or RSS measurement was performed.
