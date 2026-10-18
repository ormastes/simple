# Native Result Ok record loses array field type after try

Provisional bug ID: `native-result-ok-record-inference-20261018`. Qualified
bug DB reconciliation is pending a working full CLI.

Phase4 authority-image compilation with producer
`3c6eafef89dcae8f22db2ff5b4ea831cda494fe19b0dd847f186792f019a2951`
and immutable source `4f00255ec1ee6908b81e4db1333d95f1a8d5d7c0`
completed MIR for 232 modules: 223 succeeded and nine failed. Three errors
reported for-in collections as `I64` at native_group_phase2_scv lines 65/117
and native_group_provisional_runtime line 112. No object was emitted by that
aggregate command. These are genuine declared array fields:

- `phase2_module_roles_select_v1` returns
  `Result<Phase2ModuleSelectionV1, text>`; `included_paths` is `[text]`.
- `cold_package_ownership_capture_v1` returns
  `Result<ColdPackageOwnershipCaptureV1, text>`; `members` is an array of
  `ColdPackageOwnershipMemberV1`.
- `native_group_provisional_runtime_match_authority_v1` returns
  `Result<NativeGroupProvisionalRuntimeV1, text>`; `records` is an array of
  `Phase2SourceRecordV1`.

The temporary source workaround states each declared Ok record type on the
local binding after `?`, importing the actual capture type from its owner.
It adds no cast, changes no loop, and preserves Result error propagation,
membership checks, source validation and ownership.

Background fix owner: MIR Result-try/type propagation. In
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`,
`lower_try_expr` calls the raw integer-returning `rt_enum_payload`, then
decodes the declared Ok type only when `enum_match_expr_type(base)` recovers
a Result type. Otherwise it retains the raw integer local. This is a concrete
inspection lead, not a demonstrated complete root cause. Remove the
workarounds only after a compiler fix passes the same unannotated native
cases. Explicit source annotations themselves still require native proof.

Regression specs call real module-role selection and runtime decoding,
iterate their typed Result-record arrays and preserve exact negative error
messages. Native execution and the corrected three production MIR sites are
currently UNRUN; source review must not be presented as their qualification.

Retained native evidence:
`C:/dev/p4i3b/authority-images/logs/provisional-authority.attempt1.stderr.log`
and the complete raw
`C:/dev/p4i3b/authority-images/tmp/native-build-stderr-37292-1.log`.
