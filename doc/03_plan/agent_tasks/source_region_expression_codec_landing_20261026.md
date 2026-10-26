# Accounted expression codec early landing ledger

Target: `e8a00fd6217f4cd5234fcfc66e5cea0c551f77d3` (`release_phase3`, fetched before extraction).
Donor: `9af5545949a`, exact independently reviewed prerequisite including
cycle1 `56d2ca8a276` and cycle2 poisoned-traversal repair. Merge owner: root.

All nine extracted files are byte-identical to the reviewed donor. Every
pre-existing target file in this set is byte-identical to donor base
`b1f33e5808c`; no target change is rewound. The actual shared-account dependency
`compiler.common.loop_resource_account_v1` already exists on target and is also
byte-identical to that base. Other imports already existed on target; the sole
new common helper is included. No caller/preflight/driver activation dependency
is imported from the unrelated C4 composition tree. The tenth changed path is
this provenance ledger.

| Path | Exact donor blob | Preservation |
| --- | --- | --- |
| src/compiler/00.common/loop_codec_account_v1.spl | 1aac06353b59cd2891ed4ebb78ad2870716fafe2 | new path |
| src/compiler/10.frontend/core/flat_pool_codec.spl | 3661421970645220a270cc12f037adb563947681 | identical target/base |
| src/compiler/20.hir/hir_codec_support.spl | c3e2443c0c8be18357710d3642d095c43489ed67 | identical target/base |
| src/compiler/20.hir/generated/hir_codec.spl | 4f7db46249dc3941b1afca417e7fcfb7e9dc0309 | identical target/base |
| src/app/compiler_schema/codec_gen.spl | 5e9a53c063697deefbda9f88e6c6650bdfc1ef36 | identical target/base |
| src/compiler/50.mir/hir_expression_artifact_v1.spl | 1cc3b14db6cdc38e0f2bbfe78e24f64d53b08e82 | identical target/base |
| test/01_unit/compiler/mir/source_region_expression_codec_account_v1_spec.spl | 63fed62ab6c97c5c3cee8103056c1f3305df4f08 | new path |
| doc/bug/source_region_field_default_replay_budget_20261026.md | f143209d60439331ca2a772328d8dbd4504894af | new path |
| doc/05_design/source_region_expression_codec_account_v1.md | ca141f928d4f9a7bf9aa2ebddbefe028168b3eea | new path |

The scope is account-aware expression codec mechanics, including early stop on
poisoned encoding. The reachable expression encoder closure has40 generated
functions and no dictionary snapshot. Shared generation guards97 entries and121
loops; this does not qualify arbitrary whole-module dictionary encoding.

Evidence: independent bounded SOURCE_GO for9af; source guard parity checked
(removing inserted guards exactly recovers the prior artifact), changed diff
checks and environment guards passed in donor. Exact extraction preservation
verified here. Twelve authored specs remain UNRUN; no compiler/native jobs,
performance qualification or full verify PASS is claimed. Unchanged green
checks were not rerun for byte-identical extraction.

General field-default replay remains OPEN: actual selected-target retention,
referenced target-binding stability, ordered occurrence completeness, reset on
all archive exits, and real driver activation are separate work. Cache data and
comparison hashes never become admission. Ordinary initial compiler admission
is outside the SOURCE account; no globally bounded compiler claim is made.
