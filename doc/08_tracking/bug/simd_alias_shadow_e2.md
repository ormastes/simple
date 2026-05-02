# Bug: simd_alias_shadow_e2 — E2 scope blocker

**Filed:** 2026-05-02  
**Filed by:** E2 (Wave-E import/scope agent)  
**Status:** BLOCKED — prerequisite work missing

---

## Symptom

D5 tests F-03..F-08, F-10, V-01, V-02 fail with:

```
semantic: method 'add' not found on type 'Vec4f'
```

(and `mul`, `fma`, `lane`, `set_lane`, `reduce_sum`, `reduce_max`, `shr_logical`, `shr_arith`, `cmp_lt`)

---

## Why E2's planned fix does not apply

The task brief assumed:

> "D4's alias `type Vec4f = FixedVec<f32, 4>` defined in
> `src/lib/nogc_sync_mut/simd/aliases.spl`"

**Empirically false.** Verified by:

```
grep -rn "^type [A-Z]\|^pub type \|^export type " src/lib/nogc_sync_mut/simd/
# → zero results
```

`src/lib/nogc_sync_mut/simd/aliases.spl` contains only **function wrappers**:

```
fn vec4f_splat(v: f32) -> FixedVec<f32>: fixedvec_splat(v, 4)
fn vec4f_from_array(arr: [f32]) -> FixedVec<f32>: fixedvec_from_slice(arr, 4)
```

There is no `type Vec4f = FixedVec<f32, 4>` declaration anywhere in
`src/lib/nogc_sync_mut/simd/`. The `Vec4f` symbol visible under
`use std.simd.{Vec4f}` (if it resolves at all) is the legacy
**struct** from `src/compiler/30.types/simd_vector_types.spl`.

E2's "Option A" (lower legacy struct priority) would convert the current
"wrong type wins" error into "unresolved import Vec4f" — making things
strictly worse. The fix is blocked until D4 lands the actual type aliases.

---

## Root Cause (confirmed)

Two separate gaps must both be closed:

### Gap 1 — D4: missing `type` aliases in `aliases.spl`

`src/lib/nogc_sync_mut/simd/aliases.spl` must gain:

```
type Vec2f  = FixedVec<f32>   # lanes=2 enforced at construction
type Vec4f  = FixedVec<f32>   # lanes=4
type Vec8f  = FixedVec<f32>   # lanes=8
type Vec4d  = FixedVec<f64>   # lanes=4
type Vec4i  = FixedVec<i32>   # lanes=4
# … etc. per C2 §11.3
```

**Blocker note:** `fixed_spec.spl` comment says "avoids parser limitation
with integer const-generic arguments in type-expression position." If
`type Vec4f = FixedVec<f32, 4>` (with const N) fails to parse, the aliases
must use the runtime-lanes form (`FixedVec<f32>` + invariant at construction)
and E2's import-priority work is unblocked but trivial.

### Gap 2 — D3: type-alias expansion before trait impl lookup

Location: `src/compiler/35.semantics/resolve_strategies.spl`
Functions: `try_instance_method`, `try_trait_method`

When receiver type is `Named(sym="Vec4f", _)` and `Vec4f` is a type alias,
`get_type_symbol` returns the alias symbol, not the underlying `FixedVec`
symbol. The lookup `Vec4f__add` fails; the correct lookup would be
`FixedVec__add`.

Fix sketch: before calling `symbols.lookup_method_in_type(type_id, method)`,
check whether `type_id` is a type-alias entry in `checker.env`; if so,
resolve to the aliased symbol and retry.

Also at runtime: `eval_method_call` in
`src/compiler/10.frontend/core/interpreter/eval_ops.spl` line 428
dispatches via `val_get_struct_name(receiver) + "__" + method_name`. At
runtime a `Vec4f.splat(...)` call returns a struct with `type_name="Vec4f"`
(legacy struct), so lookup is `Vec4f__add`, which doesn't exist in the
function table (only `FixedVec__add` exists).

---

## Smallest workaround for D5 tests (today)

Until D4+D3 land, D5 tests can bypass both gaps by calling `FixedVec`
constructors directly:

```simple
# Instead of:
val v = Vec4f.splat(1.0)
val result = v.add(vb)

# Use:
val v = fixedvec_splat(1.0, 4)
val result = v.add(vb)    # struct name is "FixedVec" → FixedVec__add resolves
```

`fixedvec_splat` is exported from `src/lib/nogc_sync_mut/simd/fixed.spl`
and already registered in the function table as a module-level fn.
Tests that use `fixedvec_splat` / `fixedvec_from_slice` directly (not via
the `Vec4f` alias name) will resolve `FixedVec__add`, `FixedVec__mul` etc.
correctly because the runtime struct name is `FixedVec`.

---

## Correct fix sequence

1. **D4** lands `type Vec4f = FixedVec<f32>` (and siblings) in
   `src/lib/nogc_sync_mut/simd/aliases.spl` — confirm parser supports it
2. **E2** (or whoever picks this up): change import scope so
   `use std.simd.{Vec4f}` resolves to `src/lib/nogc_sync_mut/simd/aliases.spl`
   (Option A), not the legacy struct
3. **D3** expands the named type alias to `FixedVec` before trait-method
   lookup in `resolve_strategies.spl` and at `eval_method_call` runtime
   dispatch in `eval_ops.spl`

Steps 2 and 3 can proceed in parallel once step 1 is done.

---

## Files involved

| File | Role |
|------|------|
| `src/lib/nogc_sync_mut/simd/aliases.spl` | Needs `type Vec4f = ...` declarations (D4) |
| `src/compiler/30.types/simd_vector_types.spl` | Legacy struct — do NOT delete |
| `src/compiler/35.semantics/resolve_strategies.spl` | `try_instance_method`/`try_trait_method` — need alias expansion (D3) |
| `src/compiler/10.frontend/core/interpreter/eval_ops.spl:428` | Runtime `eval_method_call` — needs alias-to-struct-name fallback (D3) |
| `src/compiler/99.loader/module_resolver/resolution.spl` | Module path resolution — no change needed |
