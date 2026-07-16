# Struct field with an undeclared type name silently built as Infer (FIXED)

**Severity:** was medium (silent-wrong — a struct field annotated with a
genuinely non-existent type name compiled and RAN with no diagnostic, instead
of the fatal "unresolved type" HIR diagnostic every other unresolved-type
shape gets since `00b5f60ea93`)
**Found/Fixed:** 2026-07-16, r_find_infer lane
**Status:** FIXED

## Symptom

```
struct Widget:
    field_a: TotallyMissingType
    field_b: i64

fn main() -> i64:
    print(1)
    0
```

`env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build
--entry widget.spl -o out --clean` built and ran successfully (exit 0, prints
`1`) despite `TotallyMissingType` never being declared anywhere.

## Root cause

`parser_parse_type_impl` (`src/compiler/10.frontend/core/parser.spl:407-611`)
is the single shared type-annotation parser used for struct/class fields, fn
params/returns, local var annotations, etc. For a plain bareword identifier
that is not a primitive/fixed-width-integer name and not found by
`named_type_find` (i.e. genuinely never declared as a struct/class/enum/trait
anywhere in the module), it falls through every check to the catch-all:

```
return TYPE_VOID
```

`TYPE_VOID` is defined as literal `0` (`core/types.spl:212`). The flat-AST
bridge's `convert_flat_type` (`_FlatAstBridge/convert_nodes.spl:193-333`) has,
as its FIRST check:

```
if type_expr_idx <= 0:
    return Type(kind: TypeKind.Infer, span: make_span())
```

— a sentinel meaning "no type annotation was written at all" (used e.g. when
`f_types[fi]` is absent). Because `TYPE_VOID == 0`, an undeclared bareword
type name collides with this "absent annotation" sentinel and silently
becomes `TypeKind.Infer` — NOT the later, unreachable-for-0
`if type_expr_idx == TYPE_VOID: return Named("void", [])` check a few lines
down, which is dead code for this exact value. `TypeKind.Infer` then reaches
HIR as "no annotation was written," so the field's type is inferred from
usage / left untyped instead of triggering `lower_type`'s
`self.symbols.lookup_or_invalid(name)` → "unresolved type: {name}" fatal
diagnostic (`20.hir/hir_lowering/types.spl:435-446`), which correctly fires
for every OTHER shape that reaches HIR as a real `Named(name, [])` with an
unresolved name.

## Why a blanket fix is unsafe (investigated, confirmed load-bearing)

`parser_parse_type_impl`'s `TYPE_VOID` fallback is not exclusively used for
typos — it is also how **every bare generic type-parameter reference**
currently resolves. There is no type-parameter scope registry anywhere in the
parser; `struct Box<T>: value: T` sends `T` through the exact same
`named_type_find` miss → `TYPE_VOID` fallback as a genuine typo, and today's
`Box<T>`/`value: T` native-builds and runs correctly (verified: prints the
real value) by relying on that same collapse. Making ANY unresolved bareword
type fatal, unscoped, would break every generic struct/class field
(confirmed via direct probe before landing this fix). Forward-referenced
struct types (`struct A: b: B` declared before `struct B`) were also checked
and are NOT at risk — `named_type_find` already resolves them correctly
(struct names are pre-registered ahead of field parsing), so they never hit
the `TYPE_VOID` fallback at all.

## Fix (narrowly scoped to struct/class field types only)

`src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl`,
`parse_struct_or_trait_decl`'s field-parsing loop: peek the field's leading
token (kind + text) before calling `parser_parse_type()` — a pure read, no
side effect, `parser_parse_type_impl` itself reads the same two calls first.
If the call actually fell to `TYPE_VOID` AND the peeked token was a plain
bareword identifier (excludes `[T]`, `fn(...)`, `(A,B)`, `Foo<...>` shapes,
which reach `TYPE_VOID` through other branches and are out of scope) AND that
name is not one of the struct's own declared type parameters (`type_params`,
already parsed earlier in the same function) AND the name isn't the literal
`"void"` (which legitimately round-trips through this same fallback) — the
field's type is re-encoded as a synthesized `EXPR_IDENT` node
(`expr_ident(name, 0)`, the same helper used throughout this parser) instead
of `TYPE_VOID`. `convert_flat_type`'s existing `tag == EXPR_IDENT` case then
correctly rebuilds `Named(name, [])`, which HIR's already-working
"unresolved type" check picks up.

**Tag-space collision landmine (also fixed):** `expr_ident`'s returned index
is just the arena's current node count. `convert_flat_type` treats indices
`0..33` as reserved fixed `TYPE_*` constants (`TYPE_VOID=0`, `TYPE_BOOL=1`,
`TYPE_I64=2`, ... `TYPE_I32=33`) and only `34..(TYPE_UNION_BASE=500)-1` as a
real expr-arena index (documented in `convert_flat_type`'s own comment as the
"tag-space hole"). For a struct declared early in a small file (few/no
expressions parsed yet), the freshly synthesized node can land in `0..33` —
observed empirically: a naive single-call fix produced index `1`, which
`convert_flat_type` read back as `TYPE_BOOL`, silently mistyping the field as
`bool` instead of firing the diagnostic. Fixed by burning throwaway
`expr_ident` calls until the real node's index clears 33.

## Nested/generic-argument positions unaffected

The peek/override wraps only the OUTERMOST per-field `parser_parse_type()`
call. `value: Option<T>`'s inner `T` recurses into a separate
`parser_parse_type()` call inside the `Option<...>` handling and is untouched
— unchanged behavior for all nested generic-argument type references.

## Verification

All probes below via `env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1
native-build --entry ... --clean` (fresh `build/native_cache` each run).
`scripts/check/native-smoke-matrix.shs` cannot currently gate this at
origin/main tip (see
`native_build_dict_extern_regression_ca1e18c17_2026-07-16.md`, an unrelated
pre-existing P1 blocking ALL 15 probes); re-verified against known-good
pre-regression commit `7f6ec07a09b` with only this lane's patch applied:
`total=15 pass=15 fail=0 codegen_fallback_hits=0`.

- `struct Widget: field_a: TotallyMissingType` → now fails loudly:
  `error: HIR lowering error ...: unresolved type: TotallyMissingType`, no
  binary produced (was: silent success).
- `class BadClass: x: NoSuchTypeAtAll` → same loud failure (shared code path
  covers `class` too).
- `struct Box<T>: value: T` → unchanged, still native-builds and runs
  correctly (prints the real value).
- `class Pair<K, V>: key: K, value: V` → unchanged, still native-builds and
  runs correctly.
- `struct A: b: B` / `struct B: x: i64` (forward reference) → unchanged,
  still native-builds and runs correctly.
- Struct with `Dict<text, i64>`, `Option<text>`, `Result<i64, text>`, `text`,
  `bool`, `f64`, `[text]` field annotations, constructed and read → unchanged,
  still native-builds and runs correctly.

## Files changed

- `src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl`
