# SDN indexed block sequence diagnostics

Status: **AUTHORED — NOT_RUN / AWAITING_VERIFICATION**. This manual describes
source assertions, not generated test output. No runtime, build or docgen
command was executed.

Executable source:
`test/01_unit/lib/common/sdn/sdn_block_sequence_spans_spec.spl`.
Implementation: `src/lib/common/sdn/parser.spl`.

The seven authored examples cover:

| Example | Independent assertions |
| --- | --- |
| Nested lists and mappings | Numeric source coordinates for first/sibling item keys and a nested item value; parsed sibling value and item count remain unchanged. |
| ResourceList child | Exact original coordinates at indexed child metadata and nested command-array elements. |
| Duplicate scope | Repeated keys within each item produce indexed issues at the repeated key; identical keys across separate items produce no issue. |
| Whitespace and comments | Extra spaces after a dash preserve first-key columns; blank/comment lines retain later row numbers and create no comment-key span or duplicate. |
| Extra-space nesting | Normalize item-head indentation like the value parser while restoring its original key column; nested duplicate and sibling coordinates remain independent. |
| Root and normalized-item controls | Root mapping-sequence admission yields indexed array paths; a dash-prefixed key in an already normalized item body stays a literal mapping key. |
| Inline and mapping controls | Inline dictionary duplicates beneath a block item retain indexed paths and exact columns; ordinary mapping duplicates retain existing coordinates. |

Metadata traversal mirrors the value parser's item boundaries. Each item's
copied mapping body uses value-parser-normalized indentation and its original
line base; first-line diagnostic columns alone receive the original-space delta;
root admission and empty-valued mapping children dispatch block sequences
with indexed prefixes. Normalized item bodies remain mappings.
Issue scopes restart per item. The value parser is unchanged. These source
changes do not extend the accepted grammar or claim multiline-inline metadata
support beyond existing behavior.

The exact coordinates are authored numeric oracles. No decoder-derived span
is used to compute an expected coordinate. Runtime execution with matching
source/compiler/runtime receipts and positive executed-example counts remains
required before any PASS claim. The five-core aggregate limit remains in force.
