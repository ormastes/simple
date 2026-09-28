# SDN inline shared grammar candidate — implementation evidence

Status: NOT ADMITTED. Runtime verification blocked before assertions.

## Dependency and route

Based on origin/main with PR #1960 commit
`2cc416871b761d3f3c3f3edd8bfcc934e1b888ea` cherry-picked as
`53d6b1ff3c1`. The candidate uses its shared `ParseProgramV2` validator and
executor; no copied VM implementation exists in the SDN adapter.

Explicit import: `std.sdn.inline_candidate`. Call
`sdn_inline_parse_candidate_v2(source, limits)` and inspect the returned value,
token spans, committed syntax, and grammar step count. `std.sdn.parse` and
`parse_file` retain the legacy route and do not import this candidate facade.
No fallback occurs inside the candidate.

Pipeline: actual SDN source tokenizer plus candidate-local quoted-token mode ->
checked ASCII byte-span arena -> ParseProgramV2 -> committed action nodes ->
SdnValue. String escape decoding and checked integer projection are factored
into a pure scalar helper; this helper does not parse grammar.

## Implemented subset

Null and booleans are exact V2 token-literal matches. Integers guard signed
64-bit overflow. Decimal floats use the legacy decimal spelling rules and
conversion, limited to 128 spelling bytes. Bare scalar words accept ASCII
letters, digits, underscore and minus. Arrays and inline dictionaries recurse
through shared grammar calls. Dictionary keys accept bare words and quoted
strings; quoted keys retain their quote characters to match legacy behavior.
Duplicate keys use the legacy last-value-wins behavior. Quoted scalar strings
support whitespace, punctuation, escaped quotes/backslashes, newline/tab/CR
escapes, and preserve unknown escape sequences like legacy decoding.

## Deliberate rejection and divergence

Unicode, actual multiline input, block mappings, tables, comments, multiword
bare strings, numeric dictionary keys, and other punctuation in bare words are
outside the subset. Unterminated quotes and integer overflow fail explicitly.
Empty source rejects whereas legacy returns Null. The permissive legacy parser
accepts missing delimiters, empty comma pieces and missing dictionary separators;
the candidate rejects these. Tests record those cases as divergence, not parity.
No location map or issue-report parity is claimed.

Resource limits bound source/tokens, grammar/actions, nodes/children, calls,
choices and VM fuel. Temporary tokenizer allocation is bounded by source length.
Semantic projection copies each accumulated list/map on append, so large flat
collections have quadratic copying cost. VM fuel does not meter this projection;
source/node limits bound it. No startup/latency/RSS or optimized arena admission
claim is made.

## Verification

The new specification covers scalar variants, nested mixed arrays/dictionaries,
quotes/escapes, signed boundaries/overflow, malformed legacy divergences,
unsupported source, and source/token/call/choice/fuel limits. Tests invoke the
explicit public candidate facade and compare independent legacy values.

Attempted once:

`SIMPLE_LIB=src /Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple test test/01_unit/lib/structural/parse/sdn_inline_candidate_v2_spec.spl --mode=interpreter`

Exit 139 after test discovery and cover-check, before test results. Log:
`/private/tmp/sdn-inline-v2-test.log`. No seed runtime was used. A static table
inspection checked all production offsets and branch/call bounds; a quoted
alternative jump was corrected during review. This is not executable proof.
Core/library/MCP smoke, old integer-array regression, native candidate execution,
performance evidence and full Stage 4 admission remain unverified.

## Follow-up: structured issue mapping

The opt-in `sdn_inline_parse_checked_v2` API now retains lexical byte spans.
See [structured issue mapping](sdn_inline_candidate_issue_spans_v2_20260928.md)
for its coordinate contract, explicit unavailable grammar/projection positions,
and still-blocked runtime evidence. The original text-error API is preserved.
