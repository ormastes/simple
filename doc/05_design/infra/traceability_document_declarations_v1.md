# Common document dispatch and authored declarations v1

Status: implemented; scoped native tests and Astra final review pass (P0=0/P1=0). Authority: full report sections6,8,13 and original
20REQ/40AC/WP0–WP7. No narrowing or completed acceptance marks.

## Common owners and public boundary

envelope_types_v1 owns TraceCodecIssueV1/TraceSnapshotV1. qualification_types_v1
owns existing summary carriers; graph_types_v1 owns existing graph carriers.
types_v1 reexports the existing names for source compatibility. document_types_v1
owns TraceDocumentV1 variants Qualification, Graph, Declarations and explicit
TraceDocumentCodecLimitsV1. encode_v1's existing trace_document_decode_v1/encode_v1
become real family dispatch with that general limit carrier; dedicated summary
APIs keep their signatures. Current generic callers are tests and migrate
explicitly, rather than silently interpreting summary-only quotas as graph quotas.

The dispatcher performs one strict parse and exact schema.name/version validation,
then invokes public bounded family-from-value operations. No second source parse
is allowed. Raw SdnValue is not trusted: every family operation independently
validates hard limits, exact fields/types, consistency and preflight. Unknown
families/majors reject; no placeholder variants for pending families are added.
codec_fields_v1 owns shared exact fields, primitive types, identifiers, paths,
digests and deterministic unknown-field selection. graph_fields_v1 retains small
forwarders for the existing graph surface. No IO/compiler/test-runner imports.

Common limits: strict SDN, aggregate text/output bytes, max_table_records and
max_table_field_bytes for table families, max_selectors/max_diagnostics for the
existing array-based summary. One authoritative strict budget is passed to the
selected family. min(max_output_bytes, max_source_bytes) bounds canonical output.
These are explicit family quotas, not a claim that summary fields use table caps.

## Authored-intent wire contract

simple.trace.declarations major1 required root fields: schema, id, namespace,
claims, aliases, exceptions, origins. id/namespace are restricted ASCII identities.
There is no candidate digest or runtime snapshot inside committed authored intent:
the capture/extraction owner binds this data to its frozen snapshot/input manifest.
All four collection sections are named tables, including empty tables.

| table | exact columns |
|---|---|
| claims | id, from_id, relation, to_id, origin_id |
| aliases | id, from_id, to_id, origin_id |
| exceptions | id, scope_kind, subject_id, rule_id, reason, owner, review_state, expires_available, expires_at, origin_id |
| origins | id, origin_kind, path, span_available, line, column, extractor_version |

Claims use14 closed relation names: specifies, decomposes_to, accepted_by,
verified_by, targets, implemented_by, motivated_by, described_by, belongs_to,
generated_from, observed_in, produced, depends_on, supersedes. The report has14
relation rows but15 names because aliases/supersedes share a row. Aliases use
only their dedicated table, never a second claims encoding. All record IDs are
unique within their own table; typed table namespaces distinguish record roles.
Every claim/alias/exception origin_id resolves to origins. Entity IDs refer to an
external graph namespace; their existence/kinds/visibility are the resolver's
obligation, not guessed by the codec. Keep conflicting/many-to-many claims and
alias targets intact for resolution diagnostics. Do not pick the first, fold
aliases, grant eligibility or infer equivalent behavior here.

Origin kinds: explicit, annotation. Path is a nonempty repository-relative UTF8
path preserving bytes/case/newlines, without NUL/empty/dot/parent segments.
Coordinates are >=1 when span_available; otherwise both zero. Extractor version
is a restricted ASCII identity. These authored origin facts remain untrusted data;
the extraction owner must bind/check actual source positions and ownership.

Exception scope_kind: entity, feature, requirement, criterion, input_path.
subject_id is restricted identity except input_path, which uses path validation.
rule_id/owner are identities, reason nonempty UTF8. review_state: proposed,
reviewed, rejected, expired. expires_available requires canonical valid UTC
YYYY-MM-DDTHH:MM:SSZ (real calendar date, years1–9999, no leap seconds); otherwise
expires_at must be empty. Reviewed/expired are claimed states, not review receipts.
Policy resolves required expiry, current validity, owner/review proof and
applicability. The codec reads no clock and cannot turn unknown evidence into pass.

## Canonical budgets and acceptance

Strict fixed nodes45 + primitive cells; depth3; max10 columns. Rows are the sum
of all four collections, cells=5C+4A+10E+7O. Default record100000/text1MiB/
field4096/output1MiB, hard record1M/text16MiB/field1MiB/output16MiB plus strict
hard bounds. Count/text/UTF8/size-only preflight precedes indexes, rows and sort
keys. Rendering shares the SDN scalar/table writer, explicit byte stable merge
order and exact escaped-size helpers. One final LF; unordered full records sort
canonically. Single rows are bounded before escaping, never full-table concat.

TDD first executes strict-valid graph/declaration fixtures through the current
qualification-only generic facade. Assertions expect typed family acceptance,
precise duplicate/origin errors rather than arbitrary Err. Final modern SSpec
checks payloads, conflicts retained, aliases, exceptions/time shape, provenance,
same-limit budgets, canonical permutation, unsupported families/major versions
and migration of existing summary calls. Because common type/import ownership
changes, run the affected graph and summary native regression suites once at the
final source stage. Native fail-only exit codes are insufficient; use built-in
matcher flags and retain example/failure counts. Astra reviews design and final
source/oracles/evidence. Coverage, NFR, broad runtime, remaining policy/run/receipt/
full qualification/Slop families and full20/40 remain open.

## Observed implementation stage

Pre-repair acceptance12/0 and affected graph14/0, qualification15/0,
budget/order11/0 are retained separately from initial baseline4/4 ->4/0.
The public raw-value boundary uses a bounded semantic-tree walk before family
validation, including keys/headers and cumulative table rows/cells. It cannot
recover source bytes or locations. This justified O(nodes) walk is not a second
parse; CPU/RSS targets still need qualification.

The reviewed raw-boundary repair checks verified allocation-free dictionary
cardinality before keys, rejects inconsistent counts, and caps cumulative key,
header and string bytes by strict.max_source_bytes before family diagnostics.
This separate source-less text bound does not claim original spelling size.
Final native raw controls5/0, acceptance13/0 and affected regressions14/0,15/0,11/0
follow the changed production source; prior-stage evidence stays separate.
