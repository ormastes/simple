# Declared record and static method recovery

Source: `test/01_unit/compiler/mir/declared_record_method_recovery_spec.spl`.

Status: authored manual; SSpec execution and docgen are UNRUN. The source-matched native bootstrap parent is not an admitted general test host. No test result is inferred from static review.

## Static receiver regression

| Requirement | Step | Real assertion |
| --- | --- | --- |
| REQ-NATIVE-STATIC-OWNER-001 | Recover each nominal type receiver before value lowering | Invoke the actual unresolved MIR method-lowering path with empty owner hints and distinguish two nominal declaration owners with the same static method name. The emitted MIR must identify the selected owner and exclude the other owner. |
| REQ-NATIVE-STATIC-OWNER-002 | Reject a method missing from its actual owner | The actual lowering path must report exactly one missing-method error when only the other owner declares the method; it must not emit a call to that other owner. |
| REQ-NATIVE-STATIC-OWNER-003 | Keep runtime values on the instance path | A runtime parameter with a nominal declared type must not be accepted as a type-valued static receiver. Existing instance-method recovery remains exercised. |

The existing scenarios also cover exact Struct/Class instance-method recovery, missing methods, forged exact mappings, ownerless declarations, rejection of non-record owners, custom `get` precedence over runtime Dict behavior, and exclusion of type-valued receivers from instance recovery.

## Native integration evidence

The pre-fix diagnostic used two distinct nominal owners, separate declaration and implementation modules, and implicit versus explicit type façades. Both 16-module builds failed in entry-module MIR with undefined nominal receivers and unresolved-method cascades. No façade binary ran. See `doc/08_tracking/bug/native_static_method_receiver_identity.md` for the bound evidence.

The changed-producer native criteria are exact output `counter=42 other=17` from both façade forms, including normal instance calls, plus rejection of `Counter.only_other()` when only `Other` declares it. Both positive façade criteria passed with compiler `209d55d9`; the negative case correctly refused compilation but reported an extra undefined-receiver error, so the overall diagnostic failed. The focused miss-path correction and exact-one-error assertion await verification. The separate imported-generic native baseline already passed and will not be replayed unchanged.

Full compiler/core/MCP checks remain UNRUN until a suitable admitted runtime exists. A bootstrap-parent diagnostic does not qualify SSpec or the full Phase 3 host.

The focused miss-path correction subsequently passed its negative native oracle on compiler `bd86d7ac`: exactly one missing-method diagnostic, no undefined receiver, and no executable. The two positive native cases retain their original `209d55d9` evidence without replay. These narrow results do not constitute execution of this SSpec.
