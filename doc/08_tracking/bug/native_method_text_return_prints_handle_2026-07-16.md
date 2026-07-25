# Native: method returning text prints raw handle integer

**Status (2026-07-16):** RESOLVED for strict-llvm (see Resolution below);
strict-cranelift is blocked by a separate PRE-EXISTING backend failure
("Failed to declare module statics", reproduced at baseline eaee86e1e4d with
no source changes).
Originally reproduced at main tip c8f4b62261a (after the rt_dict/rt_tuple
extern-migration revert). Found while verifying
`native_method_cleanup_global_misresolution_2026-07-13` (lane method_cleanup).

A struct impl method returning `text` builds and dispatches correctly under
`native-build --entry`, but `print()` of the returned value emits a raw
runtime-handle integer instead of the string content.

Repro (dual-backend protocol):

```simple
struct Widget:
    name: text

impl Widget:
    fn describe(self) -> text:
        return "widget:" + self.name

fn main() -> i64:
    val w = Widget(name: "w1")
    print(w.describe())
    return 0
```

- Oracle (`env -u SIMPLE_BOOTSTRAP bin/simple run`): `widget:w1`
- Native (`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry ... --clean`
  then run): a raw integer such as `99089996469537` (varies per run), rc 0.

Not a regression from the 2026-07-15/16 churn: reproduces identically at
ca1e18c1744^ (pre "wip(os): checkpoint memory leveling native verification")
and at c8f4b62261a. Same-shaped programs whose methods return `i64` have full
parity (see `method_owner_dispatch` in
`scripts/check/check-native-seed-parity.shs`), so this is a text-return
decode/print gap on the method-call result path, not a dispatch defect. Likely
area: method-call result typing in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` (result local
not registered as text/runtime-string, so `print` lowers to the integer
variant).

## Source fix

HIR callable predeclaration now records complete signatures for local and
imported instance/static methods, including implicit receivers and inherited
trait defaults. MIR method-call lowering therefore receives the declared text
return shape instead of its former untyped `i64` fallback. Focused HIR/MIR
tests cover local, aliased-import, static, and inherited-default paths; the
native parity harness now includes `method_text_return` for both LLVM and
Cranelift.

## Resolution (2026-07-16, lane q_text_return)

The predeclaration fix above closed the instance-method RESULT typing (print
of `w.ret_name()` decoded correctly at tip), but the parity case still failed
because of two residual i64-mistyped locals, both root-fixed at HIR lowering:

1. **`self.<field>` inside a method body had no HIR type.** The Field-expr
   typing shim in `src/compiler/20.hir/hir_lowering/expressions.spl` only
   resolved field types for bases registered in `local_struct_types`
   (`val x = StructName(...)` bindings). A `self`/`me` base — or any typed
   param — missed it, so MIR defaulted the field local to i64 and
   `coerce_concat_operand` rendered the text field's tagged handle as a
   decimal: `"widget:" + self.name` printed `widget:98305384974848`.
   Fix: the shim now also recovers the owning struct from the base symbol's
   own declared type, falling back to `current_method_self_type` for a
   `self`/`me` base without an explicit annotation.

2. **Static impl methods lowered under a fresh UNTYPED symbol.** The parser
   marks statics `is_method=false`, so `lower_function`
   (`src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl`) never
   owner-qualified the name, missed the predeclared typed symbol
   (`Widget::category`), and defined a fresh plain `category` symbol with
   `type_ = nil`. That symbol is what MIR's `static::{Owner}::{method}`
   dispatch carries, so `resolved_call_return_type` fell back to i64 and
   `print(Widget.category())` rendered the raw handle. Renaming the symbol is
   NOT viable (the definition is also emitted from the module-functions copy
   under the plain name; a qualified call site fails to link — verified:
   ld.lld undefined `Widget.category`). Fix: the fallback definition now
   attaches the static's full `declared_callable_type` signature.

Evidence (worktree at eaee86e1e4d + fix):
- Before: native strict-llvm printed `widget:98305384974848` / `98305384974861`.
- After: parity case source prints `widget:w1` `/` `static` (rc 0), matching
  the oracle; controls pass natively with oracle parity: text-returning free
  function, method result in concat (`d + "!"`), comparison
  (`d == "widget:w1"` -> cmp_ok), direct field print, static result in concat.
- `scripts/check/native-smoke-matrix.shs`: 15/15, fail=0, fallback_hits=0.

`method_text_return_cranelift` remains blocked by the pre-existing cranelift
"Failed to declare module statics" backend failure (fires at unmodified
baseline for the same source; separate root, not a text-return typing issue).
