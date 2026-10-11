# Trace graph, SDN and evaluation detail design

Status: proposed implementation contract; local Astra review recorded, executable
qualification pending. Authoritative
schemas/identity/edge rules remain in final report sections 6–10 and 13.

## Schema boundaries

Use `std.common.sdn.parser` hardened parsing and issue reporting, followed by
typed schema validation; use `sdn_encode_canonical` for encoding. Reject
duplicate keys/headers/IDs, unknown schema majors/semantic fields, wrong types,
invalid enums, integer overflow, malformed quoting, row cardinality and missing
references. Do not downgrade parser issues into accepted data. SDN size/depth
limits apply before decoding. Decode failure cannot become an empty clean graph.

Families are `simple.trace.policy`, `.declarations`, `.graph`, `.run`,
`.qualification`, `.receipt`, and `simple.slop.message`/`.preferences`, each
version 1 initially. Encoding is UTF-8/LF with one final newline. Unordered rows
sort by canonical ID; meaningful step/attempt order has an ordinal. Empty,
absent, zero and unknown are distinct values. JSON flags and alternate structured
encodings are usage errors, including split and equals forms.

The first CLI migration emits `simple.trace.qualification` version 1. It exposes
selected snapshot/scope, completion, exit status, deterministic diagnostics and
explicit structural-only qualification; it cannot invent execution coverage.
Default and explicit SDN stdout contain one parseable document. Help is text;
progress belongs on stderr; quiet suppresses progress, not verdict. Usage/infra
failure is 2; completed violation is 1; completed selected-scope success is 0;
interruption is 130. Until exact snapshot providers are implemented, worktree
scans identify themselves as worktree and cannot be installed as commit gates.
A clean empty structural scope may return 0 with `evaluation.complete: true`
while `evaluation.qualification: incomplete` states that execution obligations
and applicability have not been established. This distinction is explicitly
tested; zero diagnostics is not a verified feature badge.

### Shared value codec and full document boundary

Source inspection of `src/lib/common/sdn/encode.spl` establishes a limitation:
`sdn_encode_canonical` only guarantees Table round-trip at the top level. A
graph document with schema/snapshot blocks and multiple named tables cannot be
passed wholesale to that encoder as a Dict containing Table values. Its inline
Dict grammar would embed raw multiline table text. This is a source-supported
design constraint, not an executed failing test or an accepted document codec.

The shared parser can also classify a malformed named table as unrecognized
and skip it. Typed validation of the surviving value cannot alone prove full
input consumption, especially for optional sections. The hardened parser or
validated adapter must account for every input token/section, allowing only
declared syntax, whitespace and comments. Strict rejection fixtures must include
malformed optional headers/rows, unexpected trailing content and extra documents.
An invalid optional section is an error, not an absent section. Do not require
authored SDN to match canonical byte formatting as a substitute for consumption;
canonical byte equality applies to the machine-output protocol contract.

The trace document adapter must reuse the common parser and scalar/inline-value
encoder while emitting valid named table sections for the report's flat graph
layout. Typed family validation precedes encoding. Top-level scalar/block
fields and named tables use a schema-defined stable section order; headers are
the family's declared field names, not arbitrary authored strings. Cells use
the shared escaping rules. Preserve ordinal/step/attempt order, and sort only
collections whose schema declares them unordered. Unsupported nested tables
fail with an actionable codec diagnostic rather than emitting malformed data.
Output has exactly one final LF. Qualification v1 contains no Table values,
so its existing common-encoder byte contract remains applicable.

`test/01_unit/app/traceability/traceability_sdn_values_spec.spl` exercises shared
value contracts for Unicode/quoted commas/escapes, row order, absent/null/empty,
signed i64 boundaries and deterministic dictionary order. These scenarios have a reported native component baseline pass, but unexpected-variant
fail-only branches require strengthening after the independently reproduced native
failure-reporting defect; they cover only a component of AC001. Separate typed-family
multi-table round-trip, strict rejections and reference closure tests are still
required. Passing only these component cases would not satisfy AC001/AC002.

### Qualification document v1 CLI adapter shape

| Path | Required type / semantics |
|---|---|
| `schema.name` | text, exactly `simple.trace.qualification` |
| `schema.version` | i64, exactly 1 |
| `snapshot.id` | nonempty canonical captured-input identity; never an invented Git revision |
| `snapshot.kind` | enum `worktree`, `index`, `git`, `sj`; adapter must actually provide that kind |
| `snapshot.complete` | bool, required captured facts available for the declared selection |
| `selection.paths` | text array of explicit selectors; empty means default reviewed roots |
| `selection.full_repository` | bool; false for the selected empty fixture; never implied by rule scope `all` |
| `evaluation.scope` | rule-group enum `all`, `src`, `spec`, `doc`; distinct from selected artifact scope |
| `evaluation.profile` | enum `worktree`, `commit`, `push`, `remote`, `audit` |
| `evaluation.kind` | enum `structural`, `evidence`; only implemented evaluation may be named |
| `evaluation.complete` | bool, mandatory selected evaluation reached terminal completion |
| `evaluation.exit_code` | i64, 0/1/2/130 under report exit semantics |
| `evaluation.qualification` | enum `satisfied`, `unsatisfied`, `incomplete`, `not_applicable_reviewed` |
| `diagnostics` | array of typed records; empty means `[]`, not absent/null |

Each diagnostic requires `code`, `severity`, `entity`, `path`, `line`, `message`,
`snapshot_id`, `rule_version`, `origin`, and `repair`; path/span availability is
explicit rather than invented. Captured-input identity binds exact selected
facts, selectors, codec/extractor/rule versions and policy/config bytes. A
worktree input identity is not current-candidate execution provenance. Qualified
execution records require the separately admitted run/evidence closure.

Canonical stdout is exactly `sdn_encode_canonical(document) + "\n"`. Usage
errors emit empty stdout and an actionable stderr diagnostic naming the rejected
option/value; no scanner result or contradictory clean document is permitted.
Infrastructure failures after captured evaluation starts emit the same typed
shape with incomplete flags/exit 2 and appropriate diagnostics. Prefix/suffix
progress, banners, extra documents and a missing final newline are invalid.

## Identity and extraction

Canonical IDs are distinct from path/symbol/scenario locators. Owned declaration
groups carry source span, authoring artifact, schema and input identity. Extract
live scenario metadata with lexical context; quoted strings/doc examples cannot
declare acceptance. Conventional source-to-unit mappings establish structure
only. Multiple surviving candidates yield ambiguity. Explicit replace/suppress
claims name their exact rule and scope; stale claims fail. Shared targets do not
duplicate test identity. Tracking fields are addressed by schema names.

## Resolution and incremental equality

Build identity/declaration/mapping registries, resolve endpoint/cardinality and
authority conflicts, record successful/negative/membership dependencies, then
evaluate obligations. Cache immutable parsed facts by content plus extractor
version. Update affected reverse closure, including unchanged incoming links.
Publish only after complete reference and manifest validation. Compare normalized
full and incremental graph/evaluator results for randomized edits and sabotage.

## Execution and qualification

An observation binds run/case/attempt, planned set, source closure, definition,
expectation, configuration, lane, binary/build-input relation, artifacts and
producer provenance. Digest strings alone prove nothing; verify bytes and trust.
Outcomes, evidence validity, applicability and qualification are separate enums.
Acceptance-only pass leaves unexecuted lower-layer obligations incomplete.
Missing planned cases, shards, cancellation and crash are incomplete. Keep all
attempts and failed retries. Legacy import preserves unknown validity.

Structural coverage counts resolved obligations; verified coverage counts
eligible satisfied obligations. Zero denominator is undetermined unless reviewed
applicability establishes otherwise. Explicit lifecycle transition is separate
from computed qualification and requires authorization plus all obligations.

## Projection and persistence

`TraceProjection` is the sole shared relation/evidence view for SDN, documents,
HTML and Slop. Stable pages bind authored structural inputs, excluding their own
outputs; immutable run reports bind exact execution candidates. Generation writes
owned temporary outputs, compares, then publishes by ownership manifest. Read-only
`--check` does not rewrite. Renderer failure preserves test results and adds an
infrastructure diagnostic. Export visibility and historical source are enforced
before rendering. Cache/migration transactions remain under existing owners.

Shared SSpec helpers: `run_trace_cli`, `decode_trace_result`,
`expect_trace_usage_error`, `expect_trace_scope_complete`,
`expect_trace_obligation_state`, `expect_trace_projection_agreement`.
Only helpers implemented with real production assertions may be invoked. Missing
later helpers remain uncreated; any scaffold must fail explicitly, never pass.

## Astra-reviewed strict codec implementation boundary (2026-10-11)

Use typed `TraceQualificationV1` and a tagged `TraceDocument` family owner under common/traceability. Decode/encode functions return located codec issues; family dispatch rejects unsupported families explicitly while their adapters remain unimplemented. The shared SDN owner must provide an opt-in strict entry returning a value plus successful full-consumption evidence, after UTF-8/resource-budget validation. It must reject unconsumed tokens, extra documents, duplicate keys/table names/headers, malformed optional sections, row-width mismatches and overflow. Preserve valid authored whitespace/comments; canonical-byte equality applies only to machine output. Do not substitute the restricted inline grammar candidate for the complete document grammar.

The first implemented increment validates quoted scalars and uses checked integer conversion. Reliable component evidence: 3 quote cases and 4 integer cases pass after actual RED. Legacy nested recovery still substitutes strings after scalar parse errors, so typed text fields alone cannot certify complete input consumption. The opt-in strict entry is now implemented locally; typed family adapters remain unimplemented. See the dated update below. Native fail-only SSpec rejection is independently defective; initial negative PASSs are invalidated, and current rejection oracles assert computed facts through built-in matchers. This limitation is recorded as a compiler/runner bug, not normalized as a permanent workaround.

### Strict shared SDN implementation update (2026-10-11)

Use std.common.sdn.strict_v1 for complete-input syntax decoding before typed
trace-family field checks. The concrete API, byte locations, grammar choices,
logical multiline-table row ownership and cumulative budgets are specified in
[sdn_strict_v1.md](sdn_strict_v1.md). Located UTF-8 validation remains under the
existing base-encoding owner; float spelling recognition is shared with canonical
encoder quoting to preserve text variants. Successful syntax carries no schema,
evidence-trust, execution or candidate-admission conclusion.

Actual component observations: legacy RED8/8; first strict GREEN16/0; review-derived
compatibility RED3/3; grouped correction GREEN10/0. Earlier and final source stages
are retained separately, and final Astra component source review passes with P0=0/P1=0. Typed qualification
and remaining family adapters, stable multi-table output/reference closure and
production CLI migration remain next. Full AC001/AC002 and later work are open.

### Typed qualification-summary implementation (2026-10-11)

TraceQualificationV1 is now implemented under std.common.traceability as the
exact summaryv1 CLI shape, with strict source decoding, typed semantic validation
and bounded canonical output. Detailed fields, unavailable-location semantics,
status consistency, ordering and authority are specified in
[traceability_qualification_v1.md](traceability_qualification_v1.md). Decoding
claimed statuses does not establish evidence eligibility or candidate admission.
Full obligation/evidence/refusal records require an explicit major2 contract and
migration preserving historical v1 claims as unverified summaries. Those records
and the remaining document families are still unimplemented.

Observed component stages: missing typed layer RED10/10, initial typed GREEN15/0,
budget/order regression RED6/1, final grouped correction GREEN11/0. Source stages
remain separate. Final source and documentation review passes with P0=0/P1=0;
full AC001/AC002 and production
CLI acceptance remain open.
