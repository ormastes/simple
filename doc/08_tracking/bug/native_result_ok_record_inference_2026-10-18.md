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
cases. The focused native comparison below proves this annotation pattern.

Regression specs call real module-role selection and runtime decoding,
iterate their typed Result-record arrays and preserve exact negative error
messages. These BDD specs and the corrected three production MIR sites are
currently UNRUN; the focused comparison does not qualify all three sites.

Focused native comparison with runtime variant `b441c88d477950d2118edf04ddaae1eefb9b5e91942dc821836d108ba776f1ab`:
the unannotated fixture failed with the expected for-in collection `I64`;
the otherwise identical typed fixture passed all 12 selected HIR, MIR and
object-codegen modules. Both call the actual module-role selection owner.
Canonical typed linking failed on an unmaterialized tracked SDK header;
that failed command remains recorded. After restoring the exact tracked
header, C-only strict completion reused the original 12 sealed COFF objects
and compiled the genuine 38 runtime C units plus canonical `/MD` entry.
Strict link passed without FORCE or ignored unresolved symbols.

The resulting executable ran exactly once: exit zero, exact 29-byte
`RESULT_RECORD_ARRAY_TRY_PASS` plus LF, empty stderr, stable pre/post SHA256
`eec6af85bf3440d7d708643bbb5c5272bc65e3ec2e8aae25fb54a3737411f7dc`.
This proves actual selected-path iteration and exact invalid-policy error
propagation for this owner. It does not qualify the other two production
sites, whole CLI, core checks or full tests.

The completion discloses missing source-witness metadata for nine standard
library capsules and post-build removal of one module-role source snapshot;
its precompile source pin matches the tracked owner. Formal SMF admission
is not claimed. Raw evidence, preserved canonical failures and strict map:
`C:/dev/simple-bootstrap-storage/scope-producer-3d9d-20261018/result-record-native-proof-setup-corrected`.
The strict completion contains `focused-execution-terminal.json`.

Retained native evidence:
`C:/dev/p4i3b/authority-images/logs/provisional-authority.attempt1.stderr.log`
and the complete raw
`C:/dev/p4i3b/authority-images/tmp/native-build-stderr-37292-1.log`.
