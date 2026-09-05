# Query Diagnostic Byte Scan Specification

Source: `test/01_unit/app/cli/query_diagnostic_byte_scan_spec.spl`

Evidence status: authored but not executed under the user-requested no-verify
override.

## Scenario: coordinates and searches preserve byte semantics

The executable fixture parses `12:7: warning: café: example`, preserving line,
column, non-ASCII message bytes, and later colons. It pins zero-column clamping
and exact malformed fallback. Search assertions prove the first match from a
requested byte offset, negative-start normalization, empty-needle bounds, a
needle longer than the source, and a match after a multibyte prefix.

## Scenario: diagnostic owners share one allocation-bounded parser

The structural fixture requires `byte_at` comparison in the canonical location
and substring-search loops and rejects per-candidate substrings. It pins a real
location-parser call in `query_commands`, pins both location parsing and
structured-separator search in `query_check`, and rejects local parser/finder
definitions so an unused import cannot satisfy the routing contract.

For N input bytes and P needle bytes, canonical location parsing is O(N), while
generic search is O(N*P) worst case and O(N) for fixed diagnostic separators.
Both use O(1) scanning state. Final field slices and higher-level structured
metadata splitting still allocate O(N) text; this tranche does not claim a
single-pass or allocation-free complete diagnostic pipeline.
