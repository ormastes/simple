# Native if/Result ownership: regression boundary retained

Status: OPEN; root cause UNDETERMINED; regression authored, execution NOT_RUN.

Upstream PR7511 documents the native Stage2 original failure and keeps its loader annotation workaround. This lane does not alter that PR, the coalesce repair, PR7534 comparison typing, or HIR expression_core/binding_types. Missing HIR expression type flags alone do not prove a compiler defect: later inference may legitimately own the join.

Added the original byte-array Ok / nested-text Err expression plus colliding variant owner, explicit-annotation control, and if-chain neighbor in test/fixtures/compiler/hir_untyped_if_result_subject/. The integration spec compiles and executes each through actual pinned native-build with isolated caches and bounded process capture, asserting byte/text payloads and all three branches. No production implementation or admission flag was changed.

Next bounded action: run the three-case integration once only when an exact admitted compiler/provider is available. Bind compiler implementation source independently from test source. Retain real diagnostics and MIR/HIR artifacts if failure occurs, then propose an owner-specific fix based on causal evidence. Prior exhausted producer/provenance budgets remain unchanged. A source-reviewed regression landing does not mark this defect fixed or codec qualification complete.

Dependency refresh 05:04 UTC: PR7511 closed as superseded by PR7536, head e11dc071418d21530309a2841a5f22e06605031f. Its unchanged OPEN untyped-if bug and annotation workaround remain; no native regression is included there. Release05c57b4368292f3df439c76cd94d4307d9311d77 includes PR7534 static-comparison typing, a separate mechanism.
