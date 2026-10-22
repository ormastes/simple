# C2 semantic declaration/body port — intermediate source work

Baseline: release `30e9aa83e94f557137dbceae22b27973d125d625`. The public full and
generated Lean module routes formerly emitted only a Type Definitions comment
instead of consuming `MirModule.types`; nominal signatures/operations explicitly
refused. The producer already registers canonical MirTypeDef rows during MIR
lowering. This port reuses reviewed declaration revision2, nominal-body revision2
and mixed-scalar donor packets from 2026-10-18, not a new parser or model.

## Compatibility and production scope

Both backend before-images exactly match the declaration donor baseline. The
current body translator, MIR instruction definitions and MIR JSON serializer
match donor dependencies. Current `mir_verify` differs only in explicit local
MirLocal/MirBlock annotations, retained unchanged. Current `mir_types` omits a
donor-only foreign-declaration carrier unused here, and reports Char size2
instead of4. Neither owner is changed; neither C2 exporter consults primitive_size.
Actual field offsets/tags and serialized type metadata are preserved, not asserted
to be a physical-layout correctness proof.

The selected Char semantic domain is Unicode scalar. Retained Lean4.30 source
`Init/Prelude.lean:2824–2841` defines Char with UInt32 storage plus validity excluding
surrogates and values above U+10FFFF. Typed Char arguments can therefore be modeled
and projected as this semantic type. The existing MIR constant translator has no
Char constructor and rejects Int/Zero with Char; this port does not fabricate a
constant adapter. Four current-base API scenarios cover typed arguments and
invalid/valid integer constant refusal across both owners. Full constant/source
and physical representation correspondence remain open requirements.

The one donor production adaptation counts accepted unique Arg rows in the
existing validation traversal instead of using Dict.len for completeness. This
preserves duplicate/range/type checks, avoids allocating a keys snapshot or adding
a pass, and addresses the retained native erased-Dict length failure documented
in `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md`. It is a
source repair, not a claim that this current binary reproduced that failure.

## Resource, identity and trust boundaries

One module-local declaration plan is shared by the two public export routes and
passed to each function; there is no global registry, cross-module raw-SymbolId
cache, process launch or new proof toolchain. Deterministic declaration planning
retains its documented O(V²+V·E) worst case and recursive type traversal. Body
validation is local to the function. No new large-module latency/RSS/stack bound
or allocation measurement is claimed. Scope is the existing finite typed input
contract, not an adversarial-size or cyclic-object-graph admission guarantee.

Exact qualified nominal identity, field order, sparse enum tags, local typing,
definition/liveness and unsupported-construct errors remain authoritative. Failed
module export returns Result error without publishing partial source. The existing
scalar/Result/global-state translator and contract/proof paths are preserved.
Recursive declarations, unions, arbitrary nominal control flow, mutation, general
calls and unsupported numeric semantics remain fail-closed. They are outstanding
full C2 requirements, not removed from the selected scope.

All four API spec files invoke actual compiler MIR and backend owners. These are
typed artifact-to-source oracles, not parsed-source integration or generated Lean
execution evidence. The retained reference Lean PASS artifacts cannot qualify
this generated output. Runtime, C1 production correspondence, C6 trusted replay,
C7 physical refinement and all broader G1–G7/C1–C7 obligations remain open where
not independently established. No compiler, test, build, proof, seed, commit or
push was run here. No signing, workflow, trust resolver or policy was modified;
authenticated SPipe admission remains a separate landing blocker.
