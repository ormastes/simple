# Document dispatch and authored declarations TDD evidence

STATUS: WARN for full verification. Scoped source/oracle/evidence review: PASS, Astra P0=0/P1=0.
Final native examples pass. Full20REQ/40AC and WP0–WP7 remain required.

The common document API dispatches qualification-summary, graph and authored
declarations major1 through one strict parse. Public family from-value operations
independently enforce structural budgets on constructed values. Common owners
hold primitive validation, text budgets, stable full-record order and envelope
types; dedicated family APIs preserve their signatures. The generic API takes
explicit document limits rather than interpreting summary quotas as table quotas.

Declarations retain many-to-many claims, conflicting aliases, exception claims
and source origins. Origin references close within the document; external entity
resolution remains a resolver obligation. Review-state and expiry are authored
data, not policy authorization or authenticated evidence. UTC validation checks
actual calendar dates without reading a clock. Rendering preflights counts,
UTF8/text and exact escaped output before indexes, rows and sort keys.

## Actual native execution stages

| Stage | Result | Meaning |
|---|---|---|
| Strict-valid missing-family baseline | 4 examples, 4 failures | Old dispatcher returned unsupported_family; syntax assertions passed |
| Initial typed implementation | 4 examples, 0 failures | Typed graph/declaration acceptance and exact duplicate/origin refusal |
| Pre-review broader acceptance | 12 examples, 0 failures | Payloads, conflicts, calendar, canonical order, output and raw-value bounds |
| Pre-repair graph regression | 14 examples, 0 failures | Renewed after common type, field, budget and order changes |
| Pre-repair qualification regression | 15 examples, 0 failures | Generic call migration and dedicated summary behavior |
| Pre-repair qualification budget/order regression | 11 examples, 0 failures | Retained resource and ordering contracts |

The acceptance fixture has97 semantic nodes,8 rows and52 cells; empty tables
have45 nodes, zero rows/cells, depth3 and max10 columns. Tests inspect typed
payloads and exact issue codes using built-in matchers. Constructed-value cases
cover row/cell/node/column/depth bounds, duplicate headers and nested wrong types.
No fail-only native exit code is used as the test verdict.

## Review-derived raw boundary repair

Astra found P1: dictionary keys materialized before the remaining-node guard,
and raw key/header bytes could reach semantic diagnostics without a text bound.
The corrected boundary checks explicitly typed, allocation-free dictionary
cardinality before keys and fails closed on negative or inconsistent counts.
Fresh native probes observed count2 for direct, matched, typed and runtime
receivers. This verifies this construction path; no general compiler fix is claimed.
Keys, headers and string values now charge a cumulative source-less text cap
using strict.max_source_bytes before family diagnostics. It is not recovered wire
size or source provenance.

The new raw controls initially showed5/4: three valid missing-text-limit failures
and one invalid oracle (zero nodes is a valid exhausted budget). That oracle was
corrected to negative nodes; the initial stage is not relabeled as four valid REDs.
Final-source native results: raw controls5/0, acceptance13/0, graph14/0,
qualification15/0 and budget/order11/0, totaling58 examples and zero failures.
Previously green regressions were renewed because production source changed.
Astra P2 distinguished adapter-invocation from key causality: the first three-family
case had a cap below valid fixture text. Only that spec changed afterward: all
three fixtures now first pass at2048 bytes, then a4608-byte injected key rejects
with text_limit. Its renewed native result is13/0. Production source and the other
four green suites are unchanged and were not rerun.

## Ownership and limitations

Construction used the immutable authorized Rust bootstrap without stub fallback.
Execution used the produced Phase2 native artifacts. Logs and frozen host hashes
live under build/native_probe and build/session; they are diagnostic evidence,
not authenticated admission receipts. The companion manual is author-written,
not generated SPipe manual-quality evidence. Earlier and final stages are distinct.

All20REQ/40AC remain open at their original scope. Remaining work includes policy,
run, receipt, full qualification major2, graph diagnostics, Slop message/preferences,
extraction/resolution, snapshots/hooks/cache, execution/DB, projections/extensions,
whole/core/lib/MCP/LSP checks, coverage, startup/latency/RSS evidence and authenticated
integration. PR2960 is unchanged and protected release refs have not moved.

Final Astra review independently matched27 source and80 artifact hashes and all
final logs: scoped PASS P0=0/P1=0. This does not authenticate admission or qualify
broader runtime gates.
