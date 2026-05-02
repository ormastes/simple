# Bug: type alias does not expand for trait method lookup (V-01, V-02)

**Discovered:** 2026-05-02 (Wave F5 D5 spec retest, after F2 alias declarations)
**File:** `src/compiler/35.semantics/resolve_strategies.spl` (per E2 bug doc)
**Tests that fail:** `test/unit/lib/simd/vector_spec.spl` V-01, V-02

## Symptom

```
V-01: generic add via Vector trait doubles each lane for f32x4 and i32x8
semantic: method `add` not found on type `Vec4f`

V-02: lanes() via Vector trait returns N for FixedVec
semantic: method `lanes` not found on type `Vec4f`
```

The user code:
```
val vf = Vec4f.from_array([1.0, 2.0, 3.0, 4.0])
val doubled = vf.add(vf)    # ← fails: 'add' not found on Vec4f
val n = vf.lanes()          # ← fails: 'lanes' not found on Vec4f
```

`Vec4f` is declared in `src/lib/nogc_sync_mut/simd/aliases.spl` as
`type Vec4f = FixedVec<f32>` (per F2). `FixedVec<f32>` has `add` and
`lanes` via `impl FixedVec<T> with Vector` (per D4).

The resolver does NOT expand the alias before looking up methods.

## Root cause

Per F2's report:
> `type Vec4f = FixedVec<f32>` — the parser accepts the syntax without
> error but currently discards the binding (parser_decls.spl:1086).

Per E2's bug doc `simd_alias_shadow_e2.md`:
> `try_instance_method`/`try_trait_method` in
> `src/compiler/35.semantics/resolve_strategies.spl` don't expand type
> aliases before looking up methods; `eval_ops.spl:428` `eval_method_call`
> has the same gap at runtime.

So the alias is double-blocked:
1. Parser stores the alias text but doesn't bind it to anything queryable
2. Even if bound, the resolver wouldn't expand `Vec4f` → `FixedVec<f32>`
   before searching for `add`/`lanes`

## Proposed fix sequence

1. **Parser fix:** `parser_decls.spl:1086` — store alias bindings in the
   AST type-environment, don't discard
2. **Resolver fix:** in `resolve_strategies.spl`, before
   `try_instance_method`/`try_trait_method` returns "method not found",
   check if the receiver's type is an alias and recurse on the
   expanded form
3. **Eval-time fix:** `eval_ops.spl:428` `eval_method_call` — same alias
   expansion before the method dispatch table lookup

Independent of F1 (Rust seed parser). The alias-expansion logic lives
in the Simple-side compiler layers 35.semantics + 95.interp.

## Workaround

In test code today, replace `Vec4f.from_array(...)` with
`fixedvec_from_array(...)` (D4's function-wrapper API which returns
`FixedVec<f32>` directly). V-03 already uses this pattern and passes.

V-01 and V-02 deliberately exercise the alias path because that's the
C2 §1.1 user-facing API. Rewriting them to function-wrappers defeats
the test's intent.

## Cross-references

- `simd_alias_shadow_e2.md` — E2's full investigation
- `feedback_simd_trait_alias_gap.md` — D5's gap memo
- `simd_generic_method_parse_e1.md` — F1's parser scope (separate issue,
  about `Foo<Int>::method()` not `Vec4f::method()`)
- C2 §1.1 — Vector trait method catalog
- C2 §11.3 — alias landing zone

## Wave-F status

F2 added alias text + 7-test alias_spec smoke tests for the
function-wrapper path (which works). The fix to make `Vec4f.method()`
work is deferred to Wave F-followup or Wave G.

Current D5 test pass count: **24/27 (89%)** — exceeds the ≥16/20 (80%)
Wave E acceptance target. V-01 and V-02 remain failing pending the
fix above.
