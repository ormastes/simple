# Typed graph codec TDD evidence

STATUS: WARN for full verification. Scoped component/source/oracle review: PASS,
Astra P0=0/P1=0. Full20REQ/40AC and WP0–WP7 remain required.

The graph data family now has explicit immutable carriers, a strict single-parse
decoder, exact table-column schemas, typed/reference validation and a canonical
named-table encoder. The existing qualification-summary major1 is unchanged;
this does not implement generic all-family dispatch or full qualification major2.
Graph values preserve untrusted manifest and provenance claims. SHA256 spelling,
references and data consistency do not authenticate file bytes, capture, policy,
execution, visibility, admission or eligibility.

## Actual bounded execution stages

| Stage | Actual native result | Interpretation |
|---|---|---|
| First baseline | 3 failures | Invalidated: unquoted colon IDs made syntax malformed |
| Corrected strict-valid baseline | 3 examples, 3 failures | Syntax assertions passed; old summary decoder returned unsupported_family for all three |
| Initial graph adapter | 3 examples, 0 failures | Original acceptance/duplicate-ID/invalid-kind cases, before later sizing edits |
| First broader acceptance | 14 examples, 10 failures | Shared escaped-size mismatch; grouped failures retained |
| Intermediate second construction | Not executed | Superseded after Astra found allocation-order P1 |
| Final broader acceptance | 14 examples, 0 failures | Final reviewed source; built-in matcher assertions, no fail-only verdict reliance |

The native size diagnostic found input bytes `[120,92,34,10,9,13]` predicted8
versus shared writer13. Binding bytes and explicitly comparing the five escape
characters corrected the helper. The compact membership expression remains a
tracked language investigation, not a silently accepted workaround or claimed
compiler fix.

Astra's allocation-order finding changed producer preflight: all strict counts,
UTF8/text limits and exact canonical output size now pass before reference indexes,
tuple keys, SDN rows or escaped sort keys. No source-stage test result has been
relabeled as a later-source pass. Three scoped verification stages were used;
unchanged green specs were not rerun.

## Exercised contracts

The final executable SSpec inspects typed input digest/role/byte count, parameter
base/role/scope/digest, edge endpoints/relation, corroborating origin identity and
coordinates, Unicode/newline paths and actual locator payloads. It covers exact
field/type/schema refusal, reordered headers, deterministic unknown-field choice,
identity/edge/record duplication, reference closure, acceptance versus supporting
test roles, base+digest parameter identity, availability/CAS constraints, alias
cardinality, containment/alias cycles and permitted dependency cycles.

Producer budgets match strict syntax: fixed70 nodes plus one per primitive cell,
depth3, max9 columns, aggregate rows/cells. A concrete fixture has146 nodes,
15 rows and76 cells. An empty graph has70 nodes and zero rows/cells. Exact-size
encoding round-trips under the same input limit; one fewer byte rejects, including
the final LF. Full-record byte sorting passes collection permutations, including
two input rows. Shared scalar sizing matches actual escaped output.

## Evidence ownership and limits

Builds used the immutable authorized Rust bootstrap for construction only, with
no stub fallback. Tests executed the produced Phase2 native artifacts. The host
record `build/session/traceability-graph-codec-20261011/evidence.json` freezes11
source hashes and16 artifact hashes; Astra independently matched them and the
final log. This is diagnostic evidence, not a Simple-generated or broker-signed
admission receipt. Reports/manuals are author-written companions, not generated
SPipe manual-quality evidence.

Remaining: all other required families and dispatcher, extraction/resolution,
candidate/cache/hook integration, authenticated execution and DB migration,
projections, Slop and extensions, whole/core/lib/MCP/LSP runtime verification,
branch coverage, latency/RSS/cycle-container performance and authenticated broker
admission. Current PR2960 is unchanged; graph work remains private. Source review
and14 green examples do not complete WP1, AC001/002 or the full20/40 scope.
