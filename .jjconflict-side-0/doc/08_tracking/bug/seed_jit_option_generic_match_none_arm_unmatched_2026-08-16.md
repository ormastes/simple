# Seed JIT: match over a `-> Option<T>` call leaves the `None` arm unmatched (nil 0x3 fall-through)

**Status:** FIXED 2026-08-16 (seed, HIR pattern lowering)
**Found via:** font registry validation — `val has_fvar = match find_table(...): Some(_): true / None: false` printed `has_fvar=error` on the JIT lane (see
`doc/08_tracking/bug/font_registry_bungee_digest_mismatch_blocks_selected_outline_path_2026-08-15.md`, which worked around it Option-free in `src/lib/common/encoding/sfnt.spl`).
Same defect class as `sfnt_fvar_option_match_nil_baremetal_2026-08-04.md`.

## Repro (minimal, pure, no imports)

`repro_match_option.spl` (kept at worktree root `/mnt/data/tmp/wave5-match/`):

```
fn f() -> Option<i64>:
    return None

fn main():
    val r = match f():
        Some(_): true
        None: false
    print("r={r}")
```

Before fix:
- `bin/simple run` (JIT lane): `r=error` — neither arm matched; the match
  expression yielded an error value. Statement-form match printed NOTHING
  (neither arm's body ran). A local `val g: Option<i64> = None` scrutinee
  yielded the raw nil tag: `s=3`.
- `SIMPLE_EXECUTION_MODE=interpreter bin/simple run`: `r=false` (correct).

Crucially, `-> i64?` (the `T?` spelling) always worked; only the explicit
generic `-> Option<T>` annotation diverged. `Some(...)` arms happened to work;
only `None` never matched.

## Root cause

`Option<T>` written as an explicit generic annotation is registered by
`hir/lower/type_resolver.rs` (`instantiate_builtin_generic_enum`, ~line 106; and
the bare-`Option` fallback ~line 210) as a `HirType::Enum` named `Option`
owning `Some`/`None` variants. Pattern lowering (twin sites
`hir/lower/expr/control.rs` and `hir/lower/stmt_lowering.rs`,
`subject_enum_owns_variant`) therefore classified the subject as a real enum
and lowered the arms to `rt_enum_check_discriminant` probes. But the RUNTIME
representation of the builtin Option is nil-boxing — `None` in expression
position lowers to the nil sentinel (0x3), `Some(x)` to a boxed optional
(`mir/lower/lowering_expr_call.rs` `("None", []) =>` / `("Option","None",...)`).
A discriminant check against the nil sentinel matches no variant, so the
`None` arm fell through and the match expression produced an error value (or
the raw 0x3). The `T?` spelling resolves to a Pointer/Option type, so it took
the correct `rt_is_none`/`rt_is_some` fast paths — hence the asymmetry.
The interpreter lane decodes nil as None independently and was correct.

## Fix

In both twin sites, compute `subject_is_builtin_option` (enum named `Option`
with exactly a payloaded `Some` and payloadless `None`) and exclude it from
`subject_enum_owns_variant`, so the builtin-Option subject takes the same
optional-shaped `rt_is_none`/`rt_is_some` fast paths as `T?`:

- `src/compiler_rust/compiler/src/hir/lower/expr/control.rs` (expression form)
- `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs` (statement form)

The user-defined-enum guard those sites exist for (an enum legitimately naming
variants `Some`/`None`) is preserved: only the exact builtin `Option` shape is
excluded.

## After fix

Both lanes agree: `r=false`; the mirrored `find_table` repro prints
`has_fvar=true` / `has_miss=false` on JIT and interpreter alike; statement-form
match prints `none`.
