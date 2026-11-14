# TargetHIR identity omits target-dependent context

Status: source repair; runtime verification unexecuted by explicit user waiver.
Source inspected: release `f998bc43600f8ae22bb7e7db75bc7edd69ecbcce`.

`target_hir_target_id` encoded architecture/subarchitecture, OS, ABI, backend
and version, but omitted build profile and CPU tier. `mir_cfg_select` consumes
the build profile when selecting debug/release arms, and `mir_target_hir_simd`
consumes CPU tier when selecting register classes. Those different results
therefore shared one TargetHIR identity for the same snapshot and region.

The context also carries collection policy, memory budget, optimization level,
trace state and admission status consumed by collection lowering. The v2 target
identity conservatively binds all 13 context fields. Length-prefixed fields
retain exact values and prevent delimiter ambiguity; the explicit v2 namespace
invalidates prior target keys. No compatibility fallback accepts an old key.
Legacy normalization, target capabilities, snapshot storage, and region identity
are unchanged. This is not full TargetHIR or cache/SCV qualification.

Five authored regression scenarios exercise real guard/SIMD readers, individual
field separation, equal inputs, separator collisions and old-key invalidation.
Existing facade golden identities are updated. Tests, builds and native
qualification were not run at the user's request.

Separate remaining audit finding: `verification_capture_target_key_v1` in
`50.mir/verification_call_lowering_v1.spl` has its own narrower context key.
Its profile/tier/subarchitecture omission is outside this TargetHIR-only fix.
