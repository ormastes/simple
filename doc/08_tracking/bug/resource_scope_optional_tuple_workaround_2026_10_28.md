# Resource-scope optional tuple metadata workaround

- id: option_generic_inner_collapses_below_named_base_2026_10_20
- status: workaround authored; controlled RED confirmed; GREEN pending
- related source fix: [PR #5154](https://github.com/ormastes/simple/pull/5154)

The authority compile at `/tmp/simple-luna-direct-phase3-20261028/authority-cache-isolated` fails E-RTI-007 for `resource_scope_systemd_metrics_v1`. Its source declares `Option<(i64,i64)>`; the old explicit Option parser branch discards tuple tags (3000–4000, below the named-type base 10000), producing Optional<Any>. RTI correctly rejects that lost declaration.

The isolated source workaround spells the identical semantic type `(i64,i64)?`. The tuple parser preserves both element tags and routes the postfix optional through the existing registry. Only the declaration spelling and bug tag change; observation parsing, failed/truncated-input rejection, tuple ordering, and physical ABI remain intact. The original resource-scope file exactly matches the authority's SHA-256 `4d76c2b02d45bb990b1a0170f50cecc172b4d80a1429929ac81f96d12fd7a24d` before editing.

The two-module fixture exports the same optional tuple shape, then checks None and both returned slots independently. Its explicit Option spelling actually fails E-RTI-007 on exact producer `8d21317328ccb2b32ba707d2485c3c8ca6c4d02592952537e7754a6d006cb116`; evidence is `/tmp/simple-resource-scope-tuple-tdd-20261028/red`. The controlled postfix run is still pending. It is not an execution of the actual resource-scope/systemctl suite, a full authority retry, or qualification of PR #5154's implementation.

Existing behavioral coverage is `test/01_unit/lib/nogc_sync_mut/io/resource_scope_evidence_spec.spl` (counter values and all failed-observation classes); that suite remains unrun in this lane. Remove the workaround only after explicit `Option<(i64,i64)>` retains Optional<Tuple<i64,i64>> metadata and passes the qualified exported-function native control on a producer containing the parser fix. No Any guard is weakened. Bug database reconciliation remains pending a qualified bug tool; this dated report does not claim a database update.
