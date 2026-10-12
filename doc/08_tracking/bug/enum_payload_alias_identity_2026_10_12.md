# Enum payload alias comparison loses container identity

REQ-ENUM-PAYLOAD-ALIAS-IDENTITY: accepting aliases for the same nominal declaration must preserve the other type components at the enum payload boundary.

The target change `a5ede0d7749d4d06c13f136ba8160081b906696d` introduced concrete false acceptances. Its array fallback ignored fixed lengths, so `[i64; 2]` compared compatible with `[i64; 3]`. Recursive calls reused scalar argument conversions, accepting different integer widths/signedness and float widths inside containers without converting their elements. Distinct same-spelling nominal IDs also compared equal when both defining owners were absent; a whole-type structural shortcut accepted equal missing IDs.

The repair keeps the existing top-level numeric/Any argument policy. A separate strict comparator covers only the previously supported alias positions: Named, Dict, Array, Slice, Optional, Tuple, and Result. Distinct IDs need the same nonempty defining owner, name, and declaration kind. An existing identical ID remains authoritative within the caller's one symbol table. Unsupported wrappers retain canonical-ID structural comparison, including its existing function-effects policy; no new wrapper alias feature is introduced.

Regression: `test/01_unit/compiler/mir/enum_payload_alias_identity_spec.spl` directly exercises the production compatibility function, including legitimate aliases, wrong/missing owners, missing IDs, generic arity, fixed lengths, nested primitive mismatches, and retained reference/pointer mutability behavior.

Validation: root and independent source reviews accepted the scoped repair; regression execution UNRUN. Scoped environment, whitespace, and spec-layout guards passed. No seed results, full compiler qualification, or memory-safety proof claimed.
