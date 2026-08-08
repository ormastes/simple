# Tuple constant index out of range reads out-of-bounds with no diagnostic

- **ID:** tuple_constant_index_out_of_range_reads_oob_no_diagnostic_2026-08-08
- **Date:** 2026-08-08
- **Status:** OPEN — reproduced; fix located but NOT landed (unverifiable on the seed, see below)
- **Severity:** medium — out-of-bounds heap read, but the index is a compile-time
  constant, so it is not runtime-attacker-controlled. Exit 0 with no diagnostic
  is still indefensible when arity is statically known.

## Symptom

```
fn main() -> i64:
    val t = (7, 9)
    print("oob: {t.5}\n")
    return 0
```

```
$ env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build \
    --source <dir> --entry-closure --entry <dir>/main.spl --cache-dir <tmp>/c --output <tmp>/b
build_rc=0            # no error, no warning
$ <tmp>/b
oob: 0
```

Index 5 on a 2-element tuple. A tuple is a raw `rt_alloc(field_count*8)` block —
16 bytes here — so `t.5` reads at offset 40, **24 bytes past the end**.
Reproduces identically without string interpolation (`val x = t.5` → `x=0`), so
it is not an interpolation artifact.

## Why nothing catches it

`emit_bounds_check_for_index` (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1293-1315`)
takes its bailout branch for a tuple base — a tuple has no length symbol and is
not a runtime array — and `return`s without emitting the `bounds_check`
intrinsic. Every MIR consumer therefore inherits the hole by construction; it is
not a Cranelift- or LLVM-specific defect.

## The bailout is already counted — cheap detection path

Established 2026-08-08 while verifying the sibling array-OOB defect: the bailout
branch is not silent internally. It increments `mir_bounds_check_bailout_count`
(exposed via `mir_bounds_check_bailouts()`) and, under
`SIMPLE_MIR_BOUNDS_DEBUG=1`, prints per-site detail:

```
[mir] bounds-check bailout #N: no len symbol for indexed base local <id> (access is UNCHECKED)
```

So `t.5` is observable today without any compiler change — set that env var on a
build and the unchecked access announces itself. Two consequences:

1. Anyone picking this up gets a zero-cost repro/verification signal, and a
   post-fix regression check can assert the counter does NOT increment for a
   tuple index.
2. The counter is a ready-made audit: a whole-program build's bailout count is
   an upper bound on unchecked indexed accesses of every kind, not just tuples.

## Contrast: runtime ARRAYS are correctly checked (verified, not assumed)

The same function handles arrays properly, so this is a tuple-specific hole and
not a general absence of bounds checking. When `len_runtime_symbol_for_hir_type`
yields nothing, `local_is_runtime_array(base_local)` still routes arrays to
`rt_array_len` and emits the intrinsic. Confirmed dynamically on 2026-08-08:
`native-build` of `xs[9]` where `xs=[10,20,30]` builds rc=0 and the binary panics
at runtime with `PANIC: bounds_check intrinsic index=9 len=3`, rc=1. An
in-bounds control (`xs[1]`→20, and `ys[2]`→3 where `ys=[1,2,3]`) runs clean,
proving the check neither over-fires nor mistakes a genuine value 3 for a
sentinel.

A tuple local is never a runtime array (`expr_dispatch.spl` — `Tuple` falls to
`case _: return false`), so it takes the bailout `return` and the access proceeds
UNCHECKED. That single predicate is the whole difference between the two rows.

## Not introduced by the 2026-08-07 tuple work — but a validation WAS lost

Commit `459dd21c5f6` routes tuple bases away from `rt_array_get` to a plain
`emit_gep`+`emit_load`. That did **not** introduce this: pre-commit the gate was
`if runtime_array or SIMPLE_BOOTSTRAP=="1"`, and a tuple local is never a
runtime array (`expr_dispatch.spl:324-332` — `Tuple` falls to `case _: return
false`; `lower_tuple_lit` never writes `runtime_array_locals`). With
`SIMPLE_BOOTSTRAP` unset the old code already took the plain GEP+load.

What the commit *did* remove, on the `SIMPLE_BOOTSTRAP=1` lane only: `rt_array_get`
(`src/compiler_rust/runtime/src/value/collections.rs:595`) begins with
`as_typed_ptr!(…, HeapObjectType::Array, …, RuntimeValue::NIL)` → `validate_heap_obj`.
On a header-less tuple block that check **fails and returns NIL** — safe-but-wrong,
which is the "empty string" symptom recorded earlier in the tuple family. Its
`len` bounds check never ran either. So that lane traded a *validated no-op* for
an *unvalidated raw GEP*.

## Correct fix (located, not landed)

The right diagnostic is a **compile error**, not a runtime guard: tuple arity is
statically known and `t.N` is a constant.

`field_tuple_element_type` (`src/compiler/20.hir/hir_lowering/expressions.spl:182-189`)
already has both operands in hand and **silently returns nil** when out of range:

```
if index >= 0 and index < element_types.len():
    return element_types[index]
nil
```

Because it returns nil for BOTH "untracked base" and "index out of range", it
cannot distinguish them — a fixer needs a separate arity lookup (e.g. a
`field_tuple_arity` helper returning -1 for an untracked base) and should emit
the error at the caller (`expressions.spl:606-620`), which holds `e.span` and
`fld_name_t`.

Scope caveat: `local_tuple_types` is populated only for `val t = (literal…)`
(`statements.spl:102`), so this catches the common case, not every tuple base.
Defense-in-depth follow-up: bind `MirTypeKind.Tuple(field_types)` rather than
`Tuple(_)` in `lower_index_expr` and reject there too.

## Why the fix was NOT landed

It was implemented at both sites and **neither fired**. Root cause of that:
`bin/simple` resolves to `bin/release/x86_64-unknown-linux-gnu/simple`, which
prints `WARNING: this Rust-built Simple binary is a bootstrap seed only`. The
`t.N` HIR desugar on this path is the **Rust seed's** lowering, not
`src/compiler/20.hir/**`, so a `.spl`-side check is unreachable here and would
have landed as unverifiable dead code.

Note this does NOT mean `.spl` edits never affect `native-build` — the
2026-08-07 `lower_tuple_lit` fix demonstrably changed native-build output
(`(1, 107362607422760, 1)` → `(1, abc, true)`). MIR lowering is consulted from
`.spl`; this particular HIR desugar is not. Establish which lane owns a phase
before assuming an edit is live.

**Unblock condition:** a deployed pure-Simple self-hosted binary, or a Rust-seed
fix in the seed's own HIR field-access lowering.

## Verification for whoever picks this up

Fixtures already on disk under the scratchpad pattern; minimal repro is the
6-line program above. Correct post-fix behaviour: build fails with
`tuple index 5 is out of range for a 2-element tuple`. Valid indices must be
unaffected — regression-check `t.0`, `t.1`, `t.0 + t.1`, whole-tuple `{t}`
interpolation, and mixed-type `(1, "abc", true)`, all of which pass today via
`sh scripts/check/check-native-tuple-to-text.shs`.
