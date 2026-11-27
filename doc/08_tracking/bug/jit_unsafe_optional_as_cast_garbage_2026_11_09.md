# JIT: `T? as u64` inside `unsafe` on a boxed `Some` yields a garbage word

- **id:** jit_unsafe_optional_as_cast_garbage_2026_11_09
- **status:** resolved (verified 2026-11-26, BF-3)
- **severity:** P2 — wrong value, but only reachable inside `unsafe:` after
  `optional_as_cast_yields_zero_2026_11_09` made the safe-code form a compile error
- **found:** 2026-11-09, while verifying that fix on a seed built from its branch

## Symptom

```simple
fn mk(v: u64) -> u64?:
    if v != 0:
        v
    else:
        nil

fn main():
    val r = mk(4275044352)
    unsafe:
        print("{r as u64}")        # JIT prints 6219716837105
    print("{(r ?? 0) as u64}")     # 4275044352 (correct)
```

`unsafe:` is the one place nil-only-in-unsafe admits treating `T?` as `T`, so the
cast is accepted there — and the Cranelift lane then reinterprets the boxed
`Option.Some` heap word instead of extracting the payload. The narrowed `?? 0` form
and the tree-walking interpreter are correct.

## Where to look

MIR lowering of `HirExprKind::Cast` when the source type is an optional
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs` /
`lowering_expr_ptr.rs`): a numeric cast from a registry-optional or `Option<T>` enum
source must first unwrap the payload (`rt_enum_payload` + `UnboxInt`), not bit-cast
the carrier. Add a `compile_and_run` test with the program above asserting
`4275044352` for the unsafe form.

## Related

- `optional_as_cast_yields_zero_2026_11_09` — the safe-code form, now rejected.

## Verification (2026-11-26, BF-3)

Already fixed in `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs` (`rt_unwrap_or_trap` + `unbox_scalar_for_raw_slot`). Verified on 2026-11-26:

- `cargo test -p simple-compiler -j 2 --test compile_and_run unsafe_option`: `5 passed; 0 failed; 48 filtered out` (`unsafe_optional_u64_as_cast_extracts_payload`, `unsafe_optional_as_cast_to_wider_int_converts_payload`, `unsafe_optional_i64_as_cast_extracts_payload`, `unsafe_optional_text_as_cast_decodes_payload`, `unsafe_option_enum_i64_as_cast_extracts_payload`).
- `cargo test -p simple-compiler -j 2 --test jit_text_and_worklist_parity`: `bug3_unsafe_optional_as_cast_jit_variants_and_interpolation` passed under `lower_to_mir_jit` + `JitCompiler::new_static()`, covering `u64? as u64`, `"{r as u64}"` interpolation, `i64? as u64`, `u64? as i64`, and `f64? as f64`.
