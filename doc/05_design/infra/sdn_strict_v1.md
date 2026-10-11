# Strict shared SDN v1 document decoding

Status: implemented locally; two native component runs are recorded separately
in the strict TDD report. Full traceability, general runtime, branch coverage,
generated manuals, performance targets and protected integration are unqualified.

## Owner and contract

`std.common.sdn.strict_v1` owns opt-in complete syntax decoding. Public text and
byte entrypoints return `Result<SdnStrictDocumentV1, SdnStrictIssueV1>` using
`SdnStrictLimitsV1` from `strict_types_v1`. Legacy parsing remains available for
its existing callers. Trace family adapters must call the strict boundary before
validating required fields, schema major, enums, references and authority.

A successful document contains the parsed `SdnValue`, the actual original-byte
cursor at EOF and cumulative node/row/cell counts. Whitespace and comments after
the root count toward consumption. No skipped optional section or scalar-error
recovery is permitted. This value carries syntax facts only; it cannot authorize
execution coverage, authenticate a receipt or qualify a candidate.

The parser maintains one forward byte cursor. Recursive descent owns nested
arrays/dictionaries, indentation owns block mappings/sequences, and balanced
delimiters own multiline table cells. Duplicate detection uses decoded names;
mapping fields and named tables occupy the same namespace. Tables require
unique nonempty decoded headers, consistent row indentation and exact width.
Blank/comment lines do not silently terminate a table before later rows.

## Grammar choices

- UTF-8 is validated without replacement. Source size is checked before the
  text entrypoint allocates its byte buffer. The existing base-encoding owner
  supplies conversion and located validation; its text-error API delegates to
  the same implementation and preserves error messages.
- LF and CRLF are accepted for layout. Bare CR layout and tabs in indentation
  are errors. Horizontal whitespace around tokens is accepted.
- Only `null`, `true` and `false` are reserved scalar words. `nil` and `~` remain
  text. Checked signed integer conversion is reused; finite decimal/scientific
  float recognition is shared with canonical encoder quoting decisions.
- The shared quoted-scalar escape rules remain authoritative, including unknown
  escapes and raw multiline content. Quoted field/header content is not layout.
- Inline arrays/dictionaries allow comments and line breaks between members.
  Empty members, missing separators and trailing commas are errors. Colons and
  equals signs in scalar text require quoting. Internal whitespace in bare
  inline-collection/table text requires quotes, avoiding absorption of a missing
  comma. Standalone, block-field and block-sequence bare text may contain spaces.
- Empty block fields and empty sequence items are null. Inline empty arrays and
  dictionaries retain their variants. A dash followed by layout starts a block
  sequence; `-7` is an integer. Sequence mapping continuations use the exact
  indentation of the first key after the dash.
- Named-table rows are deeper than their header; anonymous root-table rows use
  root indentation. Quoted cells and balanced nested values may contain physical
  newlines. Their logical row completes only after the value and row separators.

Canonical quoting of scientific-looking String values now uses the same float
recognizer as strict parsing. A text `1e3` stays text; a numeric `1e3` is Float.
Whole-family multi-table encoding still needs its typed adapter; the existing
canonical encoder does not serialize a dictionary containing nested tables.

## Budgets and diagnostics

Defaults: 1 MiB input, depth 64, 250000 nodes, 100000 rows, 1000000 cells and 256
columns per table. Hard bounds constrain caller limits: input 16 MiB, recursion
64, counters 4000000 and columns 65536. Negative/invalid configurations reject.
Nodes include decoded keys and headers. Rows/cells accumulate across sections.
Budget checks precede semantic append/commit. Empty tables permit zero row/cell
budgets; successful scalar/container input still requires its node budget.

Issue offsets and columns count original UTF-8 bytes; line and column are
one-based. Syntax issues point to the cursor where rejection was established.
UTF-8 issues use the validator's reported offending byte or invalid sequence start.
For multiply malformed sequences, continuation checks precede overlong/range
checks; the offset identifies the diagnosed failure, not a guaranteed earliest
malformed prefix across all overlapping defects.
Location computation scans a bounded prefix only on rejection. Normal parsing
does not repeatedly scan the whole document. Runtime allocation/RSS and latency
measurements remain required before accepting the selected NFR targets.

## Evidence and remaining work

The legacy boundary produced eight actual failed rejection cases. The first
strict implementation passed sixteen cases. Astra then identified compatibility
and oracle gaps; three added round-trip regressions failed before repair and ten
review-derived cases passed after grouped correction. These runs bind different
source snapshots; the earlier sixteen-case run was not repeated or relabeled as
the final source run. Exact variants/payloads and computed outcome flags use
built-in matchers because the independently recorded native fail-only defect is
still open. Exit zero is not the SSpec verdict.

Next adapters: typed `TraceQualificationV1`, then the remaining trace/Slop
families, stable multi-table output and reference closure. Production CLI and
the complete AC001/AC002 obligations remain open. Later extraction, snapshots,
runner evidence, projections and Slop retain their original 20/40 scope.
