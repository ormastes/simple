# Typed qualification-summary v1

Status: implemented locally as the next WP1 codec increment; native TDD evidence
is retained by source stage. This is untrusted summary data, not complete
qualification, admitted evidence, a candidate receipt or a lifecycle transition.
The original 20 REQ-TRC / 40 AC-TRC / WP0–WP7 scope remains required.

## Schema and ownership

The schema is `simple.trace.qualification` version 1. It has exactly `schema`,
`snapshot`, `selection`, `evaluation` and `diagnostics`, using the CLI summary
shape in the trace graph detail design. Unknown fields, missing fields, wrong
types, unsupported family/major and invalid enums reject. Invalid array members
reject the entire document rather than yielding a partially decoded array.

`std.common.traceability.types_v1` owns typed records, codec limits and issues.
`qualification_v1` owns public decode/encode and private shared semantic/value
bridges. `encode_v1` exposes the encoder facade and closed `TraceDocumentV1`
dispatch. Only the qualification variant is implemented; other families return
an explicit unsupported-family issue. Generic strict SDN parses once before
typed decoding. No fallback, skipped section or source-only result can create
an empty accepted summary.

### Status and schema evolution

Version 1 is the exact CLI summary contract. Adding full obligation evaluations,
eligible evidence and refusal records requires a separately specified major2
schema and explicit migration. It must not silently extend or reinterpret v1.
The future importer preserves v1 claims/history as unverified summary data;
it cannot fabricate missing obligation closure or execution provenance. The
major2 adapter and importer remain required implementation work.

Decoded status strings are claims. There is no eligibility, verification or
admission result type in this codec. The first structural CLI producer must use
qualification `incomplete` until the evaluator and applicable obligation/evidence
owners establish otherwise. A consistent evidence/satisfied wire record may be
preserved as data; it cannot authorize verified coverage or a done transition.

## Validation

Snapshot kinds: `worktree`, `index`, `git`, `sj`. Evaluation scopes: `all`, `src`,
`spec`, `doc`; profiles: `worktree`, `commit`, `push`, `remote`, `audit`; kinds:
`structural`, `evidence`. Qualification values: `satisfied`, `unsatisfied`,
`incomplete`, `not_applicable_reviewed`. Severity is `info`, `warning`, `error`.

Identity/code/entity fields use nonempty restricted ASCII with letters, digits
and `._:/@+-`. Paths retain actual case/Unicode; this codec does not normalize
paths, resolve aliases, authenticate claimed snapshot IDs or capture Git facts.
Rule version, message, origin and repair are nonempty text. Diagnostic origin is
attributable text, not the separately defined relationship-origin enum.

Every diagnostic has code, severity, entity, path, path/span availability, line,
column, message, snapshot ID, rule version, origin and repair. Its snapshot ID
must equal the document subject. Available path means nonempty text; unavailable
path means empty text and unavailable span. Available span requires available
path and positive one-based line/column. Unavailable span requires zero
coordinates. Repeated codes and exact repeated records are preserved.

Incomplete snapshot implies incomplete evaluation. The reverse implication is
false: snapshot capture can complete before evaluation crashes or is interrupted.
Completed evaluation uses exit0/1. Incomplete evaluation uses exit2/130 and
qualification `incomplete`. Claimed satisfied/reviewed-inapplicable requires
exit0; claimed unsatisfied requires exit1. Exit1 requires diagnostic reasons;
exit0 cannot contain error severity. Completed structural exit0 may still have
qualification `incomplete` because execution obligations remain unestablished.

For data-format preservation, exit2/130 may carry an empty diagnostic array.
The production CLI/evaluator must still report infrastructure/cancellation
reasons; this later producer requirement is not inferred or authorized by data
deserialization. Usage failures before evaluation emit stderr and empty stdout.

Typed issues have field paths and `location_available=false` with zero byte
coordinates. Strict syntax issues preserve the source location; configuration
and source-budget failures explicitly mark coordinates unavailable. No typed
field issue invents a physical span. Multiple unknown fields deterministically
select the least name under the shared text ordering, independent of iteration.

## Deterministic encoding and resources

Encoding validates caller-constructed typed values through the same semantic
rules and uses the actual shared canonical SDN encoder with exactly one LF.
Selector order is retained. Diagnostics sort by the entire canonical typed-record
encoding using stable bottom-up merge order, O(n log n); duplicate records remain
present. Ordered dictionary fields use the shared encoder. Authored whitespace is
accepted on decode; canonical byte equality is a machine-output rule only.

Limits include shared strict SDN limits plus selector count, diagnostic count,
total dynamic text bytes and output bytes. Defaults are 4096 selectors, 100000
diagnostics and 1 MiB text/output. Hard limits are 65536 selectors, 100000
diagnostics and 16 MiB text/output. Invalid configurations reject.

Before constructing values or diagnostic sort keys, typed input counts and text
are bounded. The exact schema has `37 + selectors + 27 × diagnostics` nodes;
depth is3 for empty selector/diagnostic arrays and4 when either contains records.
Encoding checks a safe output lower bound: fixed wire overhead252 bytes including
LF, diagnostic overhead164 each, array separators and raw dynamic text bytes.
Quotes, escapes and longer integer/bool spellings only increase that lower bound.
The exact final encoded size is checked against
`min(max_output_bytes, sdn.max_source_bytes)`. Successful encoding therefore
respects the same decoder input budget; escaping logic remains shared.

Decode uses strict UTF-8 validation once, then typed length/count checks. Encoding
validates caller-provided UTF-8 after early count/text/output checks. Decode does
not require an output allowance; a zero write capacity can still permit reads.
Latency, RSS and branch coverage remain unmeasured at their required full scope.

## TDD and remaining obligations

Actual syntax-only baseline: ten semantic rejection cases failed. This identifies
the missing typed layer, not a defect in syntax parsing. The first typed adapter
passed fifteen cases. Review-derived budget/order tests produced six examples
with one same-budget encoding failure; grouped corrections passed eleven final
cases. Source snapshots remain separate; unchanged passing specs were not rerun.
No synthetic fixture proves production CLI, snapshots, trust or full acceptance.

Next: migrate the production traceability CLI through this typed summary owner,
using exact captured input facts; qualify its modern SSpec command scenarios.
Then implement the remaining families, normalized graph/table/reference closure,
extraction, snapshots/admission, runner evidence, projections and Slop. Full
AC001/AC002 and later cases remain open.
