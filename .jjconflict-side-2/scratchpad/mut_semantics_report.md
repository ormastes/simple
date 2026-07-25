# Mutation-semantics silent-wrong cluster fix (#173 / #167 follow-up)

Fix lane for the defect cluster in `scratchpad/class_semantics_probe.md`:
on the NATIVE `--entry` path, the #167 copy-on-param-bind fired with no
exemptions for class-typed params, `mut` params, or `me`-method self
receivers, silently dropping caller-visible mutations.

Worktree: `/tmp/wt_mutsem` @ `f10db44f0f4` (the probe's pinned commit; the
originally-specified base `35c4b52ead6` was broken for ALL native builds by
an unrelated half-swept lexer migration, so the probe base was used to keep
oracle/native comparisons apples-to-apples).
Patch: `scratchpad/mut_semantics.patch` (apply with `git apply` from repo root).

## Root causes fixed

1. **Class/struct conflation at the flat-AST bridge** — `class` decls were
   inserted into `module.structs` with the parser's `decl_is_value_type` bit
   discarded; `module.classes` stayed `{}`. Downstream, 50.mir's
   `struct_field_order.has(name)` was true for classes, so #167's
   copy-on-param-bind materialized a private copy of every class param
   (self receivers included) and threw the mutations away.
2. **`mut` param modifier discarded by the parser** —
   `parser_skip_mut_if_present()` consumed the token and dropped the bit, so
   even the documented "caller observes the mutation" spelling was copied.
   (Found while fixing: `ast_decl_text_set` silently no-ops for any field
   outside its NAME/PARAM_NAMES/... whitelist — a first attempt to store the
   flags as "PARAM_MUTS" through it was silently dropped; a dedicated
   idx-keyed side table is used instead.)
3. **`me`-method self receiver not exempted** — `self` lowers as an ordinary
   Named param, so the struct copy also disconnected `me` methods from their
   receiver (structs AND classes).

## Changes per anchor

| File | Change |
|---|---|
| `src/compiler/10.frontend/parser_types.spl` | `Struct.is_value_type: bool` + `Param.is_mut: bool` fields |
| `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` | tag-3 branch now sets `is_value_type: decl_get_is_value_type(idx) != 0` on the `Struct` record (+ import) |
| `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` | `convert_decl_fn` / `convert_decl_extern_fn` read `decl_get_param_muts` and set `Param.is_mut` (+ import) |
| `src/compiler/10.frontend/core/_Ast/decl_nodes.spl` | `decl_param_muts_store: Dict<i64, text>` side table + `decl_set_param_muts` / `decl_get_param_muts` (NOT via `ast_decl_text_set` — whitelist drop, see above) |
| `src/compiler/10.frontend/core/_Ast/module_state.spl` | clear `decl_param_muts_store` on arena reset (decl idx reuse across parses) |
| `src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl` | `parser_skip_mut_if_present() -> i64` (1 = consumed `mut`); `parse_fn_decl` collects `param_muts` and calls `decl_set_param_muts` (+ import) |
| `src/compiler/20.hir/hir_definitions.spl` | `HirStruct.is_value_type: bool` + `HirParam.is_mut: bool` |
| `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl` | `lower_struct` threads `is_value_type`; `lower_param` threads `is_mut: p.is_mut == true`; the 2 other HirParam sites set `is_mut: false` |
| `src/compiler/50.mir/mir_lowering_types.spl` | `MirLowering.struct_is_value_type: Dict<text, bool>` |
| `src/compiler/50.mir/_MirLowering/module_lowering.spl` | populate `struct_is_value_type` alongside `struct_field_order`; init `{}` in `MirLowering.new()`; corrected the stale "structs only, not classes" comment |
| `src/compiler/50.mir/_MirLowering/function_lowering.spl` | **the gate**: copy fires only `if is_value_type and not is_me_self_receiver and not is_mut_param` |
| `src/compiler/80.driver/driver_pipeline.spl` | init `struct_is_value_type: {}` in the 2 literal `MirLowering(...)` constructions (missing field read as nil → "cannot index assign to field of type nil") |

`param.is_mut == true` / defensive reads everywhere: HirParams built by
lane-forbidden sites (e.g. `20.hir/hir_lowering/expressions.spl:479` closure
lowering) leave the field unset (nil) which must mean "not mut" → the safe,
pre-existing copy behavior. That file was NOT touched.

## Battery (native `--entry`, fixtures from scratchpad/class_probe_fixtures/)

Oracle = `env -u SIMPLE_BOOTSTRAP bin/simple run` (per probe, reliable for
param/method cases; alias rows judged by spec-by-construction due to the
documented interp `val`-alias landmine).

| Fixture | Shape | Before (native) | After (native) | Expected | Verdict |
|---|---|---|---|---|---|
| c1_class_arg_mutate | class, plain `fn bump(c: C)` | 1 | **41** | 41 | FIXED |
| c1m_class_mut_param | class, `fn bump(mut c: C)` | 1 | **41** | 41 | FIXED |
| c2_class_alias_mutate | class, `val b = a` alias | 41 | 41 | 41 | still correct |
| c2b_class_var_alias | class, `var b = a` alias | 41 | 41 | 41 | still correct |
| c3_class_in_array | class, `arr[0].x = 41` | 41 | 41 | 41 | still correct |
| c4_class_as_struct_field | class, `h.c.x = 41` chain | 41 | 41 | 41 | still correct |
| c5_class_method_mutate_self | class, plain-`fn` self ×2 | 1 | **41** | 41 | FIXED (class exempt from copy) |
| c5m_class_me_method | class, `me inc()` ×2 | 1 | **41** | 41 | FIXED |
| s1_struct_arg_mutate | struct, plain `fn bump(c: C)` | 1 | 1 | 1 | **REGRESSION GUARD: copy preserved** |
| s1m_struct_mut_param | struct, `fn bump(mut c: C)` | 1 | **41** | 41 (oracle 41, doc case 2) | FIXED |
| s2_struct_alias_mutate | struct, `val b = a` alias | 41 | 41 | 1 | still wrong — bonus defect (1), documented below |
| s3_struct_in_array | struct, `arr[0].x = 41` | 41 | 41 | 41 | still correct |
| s4_struct_as_struct_field | struct, `h.c.x = 41` chain | 41 | 41 | 41 | still correct |
| s5_struct_method_mutate_self | struct, plain-`fn` self ×2 | 1 | 1 | compile error per W1006 doc | deliberately unchanged (see below) |
| s5m_struct_me_method | struct, `me inc()` ×2 | 1 | **41** | 41 | FIXED |
| multi_construct | class+struct+me+mut+plain+loop | — | c=113;x=11;y=2 | c=113;x=11;y=2 | PASS |
| s_readonly_method | struct, read-only `fn get_x()` | 7 | 7 | 7 | still correct |

Oracle spot-checks (interp): c1m=41, c5m=41, s5m=41, s1=1, s1m=41 — native
now matches the oracle on every sanctioned-mutation row.

## Regression guards

- `s1_struct_arg_mutate` (plain struct param) still prints **1** — the #167
  copy is preserved for genuine value-type params.
- `s5_struct_method_mutate_self` (plain-`fn` self mutation on struct) still
  prints 1 — deliberately unchanged: that shape is *documented* as a
  compile-time rejection (W1006), and un-copying it would silently make an
  unsanctioned mutation "work". See "Documented, out of scope" below.
- multi-construct test (class + struct + me methods + mut param + plain
  param + loop in one binary) — all three observables correct.
- Full native smoke matrix (`sh scripts/check/native-smoke-matrix.shs`):
  **total=15 pass=14 fail=1 xfail=0 xpass=0 codegen_fallback_hits=0**; the
  only FAIL is `option_nil_check` (the pre-existing allowed failure) —
  identical to the pre-fix baseline run of the same matrix in this worktree,
  including the struct-value-semantics cases (`struct_field` PASS 71/71).
- Read-only struct `fn` method (`get_x()` on a copied receiver) still
  returns the right value (7) — copy path for non-`me` struct methods
  unchanged.

## Documented, out of scope (from the probe's bonus list)

1. **Struct local-alias copy missing** (`val b = a; b.x = 41` leaks into `a`;
   probe row 6b): NOT fixed by this threading — the #167 copy exists only at
   parameter-bind time; local `val`/`var` rebind lowering emits no aggregate
   copy at all (see `20.hir/hir_lowering/statements.spl` decl lowering).
   Verified still present after this fix (s2 prints 41, spec says 1). Needs
   its own follow-up; the `is_value_type` bit this fix threads to 50.mir
   (`struct_is_value_type`) is exactly the signal that follow-up needs.
2. **W1006 mut-capability enforcement absent from native `--entry`**: the JIT
   path statically rejects plain-`fn` param / non-`me` self mutation; the
   native path compiles them silently. Out of scope per task; the gate here
   deliberately keeps the copy for those shapes so they don't silently gain
   unsanctioned mutation semantics.
3. **`mut` params in class-body methods**: `parse_class_body_method`
   (parser_decls_use.spl) never accepted a `mut` param modifier in the first
   place (no `parser_skip_mut_if_present` call); method params therefore have
   no mut flags recorded (empty list → all false → copy for struct params).
   Pre-existing parser limitation, unchanged.

## Verify commands

```
env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry FIXTURE.spl -o OUT --clean && OUT
sh scripts/check/native-smoke-matrix.shs
```
