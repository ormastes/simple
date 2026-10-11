# Typed normalized trace graph codec v1

Status: graph component implemented; scoped native14/0 and Astra PASS,
full verification WARN and no execution admission. Authority:
final report sections6–8 and20REQ/40AC, existing shared graph architecture.
This increment implements the graph data family and its complete typed reference
closure; policy/declaration/run/receipt/Slop families remain required afterward.

## Public owners

std.common.traceability.graph_types_v1 owns versioned immutable carriers.
graph_schema_v1 validates data and reference closure without IO. graph_decode_v1
uses the strict common SDN parser exactly once. graph_encode_v1 uses the common
scalar/table writer and schema-owned section/header order; graph_v1 exposes these
public operations. Existing qualification-summary v1 is preserved; its family
union/dispatcher is not silently changed. Generic all-family dispatch follows
a separate common-envelope refactor once the additional families exist.

## Wire shape and authority

Required root fields: schema, snapshot, manifest, inputs, nodes, test_definitions,
edges, edge_origins, locators. schema.name=simple.trace.graph/version1. Snapshot
uses the existing id/kind/complete contract (worktree/index/git/sj). Manifest has
input_set_id, extractor_version, rules_version, policy_id, complete. All are
required; version/identity text is nonempty restricted ASCII where appropriate.
Snapshot.complete requires manifest.complete, but these booleans are untrusted
data. Parsing cannot establish admitted capture, eligible execution, visibility
permission, actual input-byte hashes or trusted policy. App providers and evidence
verification must validate those facts before publishing/admitting a generation.
The codec validates SHA256 spelling, not artifact bytes or producer provenance.

All six collection sections are named tables, including empty tables. Columns:

- inputs: path,sha256,bytes,role (source/test/document/policy/declaration/evidence).
- nodes: id,kind,title. IDs reuse existing identities; paths/titles are not IDs.
- test_definitions: entity_id,test_kind,identity_scope,definition_id,parameter_digest_available,parameter_digest.
- edges: id,from_id,relation,to_id.
- edge_origins: edge_id,origin_kind,origin_id,declaration_path_available,declaration_path,span_available,line,column,extractor_version.
- locators: entity_id,path_available,path,locator_kind,locator.

Headers are addressed by name and may be reordered on input; missing, unknown or
duplicate fields reject. Cells have exact primitive types; absent/null/empty are
not interchangeable. Paths preserve UTF8/case/newlines, are repository-relative
without NUL, empty/dot/parent segments. IDs use restricted ASCII grammar. Source
bytes and counters are nonnegative i64. Digest values are exactly64 lowercasehex.
Unordered rows encode in full canonical-record byte order, with one finalLF.
No nested Table is passed to the generic inline-Dict encoder.

## Semantic closure

Reject duplicate input paths/node IDs/edge IDs/test definitions/locator tuples/
origin tuples, duplicate resolved endpoint+relation tuples and duplicate parameter
sets. Every test_case and parameterized_case has a matching test definition;
parameterized definitions refer to a base test_case and retain its kind. Kinds
acceptance/unit/integration/component/system/performance stay distinct. Ordinary
definition_id equals entity_id; parameterized cases require available digest.

Every edge endpoint/origin edge/locator entity resolves. Every edge has provenance;
several distinct origins corroborate one edge without duplicating it. Located
origins and file/symbol/scenario/section locators resolve to manifest input paths.
Availability booleans require actual text and zero unavailable coordinates. CAS
locators are explicit sha256 references with unavailable repo path.

Relation endpoints follow report6.2; accepted_by only targets acceptance cases,
verified_by only unit/integration/component. Alias/supersedes endpoints retain
compatible kinds and test roles. Reject cycles for belongs_to and aliases using
bounded iterative graph traversal; dependency cycles remain permitted. Alias
resolution has at most one outgoing canonical target. This is structural data
validation, not authority/conflict resolution or eligibility evaluation.

## Bounds and performance

Strict source/rows/cells/nodes/depth limits apply before typed decoding. Codec
limits bound total records, aggregate UTF8 text bytes, per-field bytes and output
bytes. Encoding preflights typed counts/text before constructing SDN rows, uses
remaining-budget arithmetic, validates schema/reference closure, and renders
bounded individual rows before joining. Full-record stable mergesort is O(nlogn);
reference dictionaries and per-relation cycle checks avoid pairwise scans. No IO,
clock, processes, GUI, compiler or test runner imports enter this domain owner.
Default source/output1MiB, text1MiB, field4096bytes, total100000records; hard bounds
come from strict SDN plus <=16MiB text/output, <=1MiB field and <=1000000records.
No startup/latency/RSS target is claimed without host receipts.

## TDD and acceptance

Initial baseline uses the existing summary decoder, which explicitly rejects
this family. Assertions require valid graph acceptance and specific semantic
rejection reasons; broad Err alone is insufficient. Final graph specs inspect
actual typed node/edge/origin/test/locator/input payloads, Unicode/comma/empty
values, multiple named sections, strict syntax, duplicate identities, reference
closure, endpoint/test-role restrictions, cycles and bounded encode/decode.
Built-in assertions observe payloads; fail-only native verdicts are not trusted.
Astra reviews this design before implementation and final source/oracles after
execution. These component cases do not complete AC001/002 or WP1/all20/40.

## Frozen concrete v1 contract after Astra review

Closed node kinds: feature, requirement, criterion, test_suite, test_case,
parameterized_case, source_file, symbol, component, layer, transform, document,
research_section, design_section, architecture_section, generated_document,
graph, observation, evidence_artifact, exception, decision, bug.
Closed identity_scope: stable, revision. Closed origin_kind: explicit,
annotation, convention, compiler_index, runtime_observation. Closed locator_kind:
file, symbol, scenario, section, cas. Test kinds remain the six roles above.

Exactly one test_definition is required per test_case/parameterized_case;
other node kinds cannot have one. Ordinary definition_id equals entity_id and
digest availability is false with empty digest. A parameterized case references
an ordinary test_case, inherits its test_kind and identity_scope, and requires a
lowercase SHA256 digest. Duplicate parameter identity is the pair
(definition_id, parameter_digest); distinct base definitions may share a digest.
origin_id is a restricted-ASCII identity of an external extracted provenance
record, not a node reference. Its resolution/authentication belongs to the
declarations/extraction owner; this graph preserves the claim without trusting it.
Unavailable paths/locators use empty text, unavailable coordinates are zero.
CAS locator is exactly `sha256:` followed by 64 lowercase hex digits, requires
path_available=false/path empty; other locator kinds require a manifest path.
File locator is empty; symbol/scenario/section locator text is nonempty.

Concrete allowed endpoints (T = test_case or parameterized_case):

| relation | from | to |
|---|---|---|
| specifies | feature | requirement |
| decomposes_to | requirement | criterion |
| accepted_by | criterion | T with acceptance role |
| verified_by | requirement, criterion | T with unit/integration/component role |
| targets | T | source_file, symbol, component |
| implemented_by | feature, requirement | source_file, symbol, component |
| motivated_by | feature, requirement | research_section, decision |
| described_by | feature, component | design_section, architecture_section |
| belongs_to | all closed node kinds | component, layer, feature |
| generated_from | generated_document | test_suite, graph |
| observed_in | T | observation |
| produced | observation | evidence_artifact |
| depends_on | component, symbol, T | component, symbol, T, source_file |
| aliases, supersedes | any closed kind | same kind; tests additionally same role/scope |

All structural membership endpoints are permitted because architecture entities
also participate in the report's compound ownership view. belongs_to and aliases
are acyclic; aliases additionally allows at most one outgoing edge per entity.
Each edge needs at least one origin; dedup keys are full primitive record tuples
encoded unambiguously, never delimiter concatenation of arbitrary text.
Resolved endpoints here mean existing node IDs, without alias folding. Distinct
alias declarations retain their original endpoints rather than collapsing into
one canonical self-edge. Claims-to-alias resolution belongs to the resolver.

Producer preflight computes row=sum(collection lengths), cells=4I+3N+6T+4E+
9O+5L, nodes=70+cells, depth=3, columns=9. Counts use remaining-budget additions
with bounded multiplicands. Enforce all strict budgets before constructing table
rows or canonical sort keys. Count exact shared scalar escaped sizes plus schema/
headers/indentation/separators/final LF before rendering; every scalar and row is
bounded before allocation. Effective output cap is min(max_output_bytes,
sdn.max_source_bytes). UTF8 text is validated before encoding. Full-record sort
uses explicit byte comparison, avoiding native text-order ambiguity.

Baseline evidence: the first malformed unquoted-ID run is invalidated. Corrected
strict-valid source produced 3 examples/3 failures, each unsupported_family,
with independent strict syntax assertions passing. This is missing-family RED,
not semantic validation coverage or admission.

## Implemented evidence boundary

Public graph decode/encode/validate live in graph_v1; graph_budget_v1 and
graph_fields_v1 own bounded primitive validation. graph_wire_v1 shares common
SDN escaping and its exact text-size helper. Encoding runs count/text and exact
size-only preflight before reference indexes or any SDN rows/escaped sort keys,
then retains per-row/final-size defenses. Unknown semantic fields are selected
by deterministic byte order. Abstract traversal is bounded/iterative; container
mutation costs and latency/RSS are not yet measured or qualified.

Actual stages are strict-valid missing-family3/3, initial adapter3/0, broader
acceptance14/10, superseded unexecuted artifact, final14/0. Astra source/oracle
and final hash/log reconciliation PASS P0=0/P1=0. No full WP1/20REQ/40AC,
generic-family dispatcher, generated-manual or admission PASS follows.
