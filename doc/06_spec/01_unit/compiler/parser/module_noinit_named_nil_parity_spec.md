# Bare named module variables preserve explicit-nil semantics

Status: **UNRUN — source candidate awaiting independent Astra review and the
root Phase3 owner's qualified engine**. This hand-authored manual describes
`test/01_unit/compiler/parser/module_noinit_named_nil_parity_spec.spl`; it is
not generated execution evidence.

Requirement: `REQ-NOINIT-NAMED-NIL-PARITY`.
Bug: `p4p2_flat_parser_noinit_module_var_struct_and_fn_types_2026-10-20`.
Baseline: `471ccc083397fb17812ba43459b233e7cd3dfde2`.

The named Astra guide selects an existing language behavior: a bare named
module variable has the same initializer and annotation as an explicit
`var slot: ExactType = nil`. It remains nil until assigned. No materialized
zero-field record is implied. The exact local named-tag guard also admits
interned forward/unknown names and Any, leaving their semantic resolution to
the existing downstream owner.

| Scenario | Real observable assertions |
|---|---|
| Nil then persistent assignment | Two actual module globals, one bare and one explicit nil, begin nil; independent helper assignments/readbacks retain 17/29 and then 43/61 |
| Exact AST parity | Production checked parser retains both declaration names, the same exact named annotation, one initializer each, and actual NilLit nodes |
| Forward/unknown/Any AST parity | Both spellings preserve the registered written name rather than adding declaration-order rules |
| Downstream parity | Actual full frontend and HIR lowering produce equal error lists and global counts for forward, unknown and Any fixture pairs |
| EOF and semicolon boundaries | Checked parser accepts the bare named form only at actual declaration boundaries |
| First expression index zero | The actual generated NilLit may occupy arena expression index 0 and remains admitted |
| Persistent MIR storage | Actual frontend/HIR/MIR providers produce one owner-qualified mutable static and matching lookup mirror; assignment and read instructions target that exact global symbol; dynamic initialization stores the actual lowered nil word once |
| Malformed named declaration | Trailing garbage still returns a parser error |
| Array contract boundary | Named-element and callable noinit fixed arrays continue returning errors under the pending contract HOLD |
| Scalar array control | Existing bool fixed-array noinit parsing remains accepted |
| Explicit record constructor | Existing materialized-record initialization remains accepted |

The spec calls actual production providers and inspects their typed results.
It does not replace parser/storage logic or use source-substring assertions as
storage evidence. The executable fixture never reads a nil record's field or
invokes an unassigned callable. The provider comparisons do not select a new
unknown-type resolution rule; they require parity with existing explicit nil.

The focused regression was written and hashed while the production parser
owner was unchanged, before the implementation edit. No test, build, compiler,
bootstrap, new runner, or Rust fallback was executed by this owner.

The original aggregate red acceptance spec/manual remain unchanged. Their
array requirements are OPEN and UNRUN. Passing this focused spec would qualify
only the named nil parity subset; it would not close the full bug or authorize
removal of any consumer initializer/workaround tag. Array/callable contract
implementation awaits the user's actual selection and persistent typed-storage
proof. Root owns the qualified-engine test queue and subsequent landing.
