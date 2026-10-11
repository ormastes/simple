# Current traceability implementation baseline

Pinned source: `a9777ac75fa5d64c6741de8981a9d13815990179`.
Isolated worktree: `/home/yoon/dev/simple-traceability-sdn-slop-20261010`.
Branch: `work/traceability-sdn-slop-20261010`. Owner: Codex root.
The original checkout contains unrelated work and is not an edit target.

| Surface | Observed behavior | Required change |
|---|---|---|
| `src/app/traceability/main.spl` | JSON flags/output, text default; loose unknown-option parsing | SDN default; reject obsolete formats; explicit usage/infra exit 2 |
| `_TraceabilityCore/config_and_analysis.spl` | Mutable filesystem collection; SDN excluded; raw requirement substring extraction | Snapshot facts, owned semantic declarations, tracking SDN ingestion |
| `_TraceabilityCore/manifest_and_report.spl` | JSON serializer; virtual manifest helpers | Shared SDN projection and immutable input identity |
| `src/app/tracking/main.spl` | Positional nonblank done-row checks | Typed field names and graph/evidence qualification |
| `std.common.sdn.parser` / `encode` | Existing shared parser, issue reporting, hardened entry point and canonical writer | Reuse; schema wrapper rejects duplicate/unknown/type/enum/reference issues |
| `std.test_runner.test_db_compat.RunnerTestDb` | Unified DB owner, run IDs, result and completion updates | Extend this owner for planned/actual immutable observations and finalization |
| `spipe_docgen/evidence_loader.spl` | Parsed sidecars render without provenance admission | Versioned legacy import; truthful admission before verified rendering |
| Hooks/required gates | Broad pre-commit generation; BASE manifest with candidate executable trust gap | Bounded exact snapshots and independently trusted executable/policy |
| Traceability integration tests | Require JSON success | Replace obsolete expectation with parsed SDN and explicit rejection |

Astra inspected these paths at the pinned revision and confirmed WP0–WP7
remain unfinished. See [review record](../../09_report/traceability_sdn_slop_astra_review_2026-10-10.md).

## Runtime admission finding

The original `bin/release/aarch64-unknown-linux-gnu/simple --version` reports
that it is a Rust-built bootstrap seed. The isolated checkout has no released
runtime. Known `build/bootstrap/stage3/.../stage2-runtime-authority/simple`
belongs to a compiler bootstrap lane. Repository rules explicitly exclude
both from general SPipe/docgen/test qualification. No Stage4 artifact was
found in the checked standalone/release/stage4 locations.

Required next execution input: an immutable admitted general-tool runtime,
binary digest, producer and source-input receipts, supported test/docgen CLI,
and isolated output/cache configuration. No test was executed using a seed.
No RED/GREEN/PASS is claimed. Context-mode execution tools returned exit -1;
bounded read-only shell summaries were used for this inventory.

## Phase2 execution update

The user authorized bootstrap or Phase2 use. A pure-Simple construction-stage
compiler at producer source `57d83549f09b374ff9105018896843d4f8ff00e9` was
copied to owned `build/traceability/toolchain/phase2-simple` and its digest
verified as `e9e8762c79e47d1c0db418d2a8ff5d5eda7b1ef8744ccff32227ae7463926491`.
Producer record states construction-only/Phase3 pending. Its help supports only
native-build and SMF compile, so general-tool support is not inferred.
`test/04_smoke/bootstrap_hello_world.spl` compiled and executed successfully:
exit 0 and `hello`. The full-CLI build initially failed missing OS/plugin roots;
a cache-preserving corrected attempt and a focused trace CLI build are underway.
All results retain Phase2 producer labeling and isolated cache/output paths.

## Continuation findings after bounded bootstrap work

The previously in-flight builds are terminal. Two owned Phase2 compiler probes
constructed and passed fresh HelloWorld; the final production traceability
construction failed at MIR. The third prerequisite cycle exhausted the user
cap; no compiler rebuilds were started in this continuation. See
[remaining diagnostics](../../08_tracking/bug/phase2_traceability_mir_gate_2026-10-10.md).
Read-only external-state checks found known bootstrap jobs terminal and no
usable general test runtime. A newly observed beta qualification candidate was
removed by its owner before help execution; its fix2/fix3 records report exit
1/3. Existence or construction size alone therefore does not prove availability.

Shared codec inspection uncovered a full-document design gap: canonical Table
round-trip is documented only at top level. Trace graph named sections require
an adapter that emits valid multi-table SDN using shared scalar escaping, not
an inline Dict containing raw Table values. Parser block-table failure can be
silently classified as unrecognized, so full-document consumption is an explicit
decoder obligation even for optional sections. Astra reviewed these findings.

Four modern shared-value SSpec cases are authored in
`test/01_unit/app/traceability/traceability_sdn_values_spec.spl`. They exercise
real existing encoder/parser behavior and are NOT RUN. They address part of
AC001; typed-family round-trip/rejection, execution, provenance, hooks, projections
and Slop remain outstanding. No source inspection or authored test is called
RED/GREEN, admission, or full feature completion.
