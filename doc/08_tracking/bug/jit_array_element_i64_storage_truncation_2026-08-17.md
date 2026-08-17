# An `i64` stored in an array is TRUNCATED under the JIT (data loss, not a print defect)

- **Filed:** 2026-08-17
- **Status:** OPEN (P1)
- **Severity:** High — silent wrong-answer arithmetic. The value itself is
  corrupted in storage; every later read, comparison and arithmetic operation on
  it is wrong. This is not a formatting problem.
- **Component:** Rust seed, cranelift/JIT path (`bin/simple run`, and every
  non-`interpreter` value of `SIMPLE_EXECUTION_MODE`). The tree-walk interpreter
  is correct.
- **Found by:** the i64-interpolation fix in
  `stage3_numeric_interpolation_slot_corruption_2026-08-13.md`. It was the ONE
  line the parity probe still diverged on after that fix landed, which is how it
  was distinguished from the rendering defect it had been hiding behind.

## Repro

```
fn main():
    var arr: [i64] = [9223372036854775807]
    val e: i64 = arr[0]
    print(e)
    print(e == 9223372036854775807)
    print(e + 0)
main()
```

Binary: an isolated build of current HEAD plus the interpolation fix
(`/mnt/data/cargo-i64interp-e29ebf0f/release/simple`; `bin/simple` was not
rebuilt or redeployed). The same divergence is present on the deployed stale
seed.

| expression | `SIMPLE_EXECUTION_MODE=interpreter` | `SIMPLE_EXECUTION_MODE=jit` |
|---|---|---|
| `print(e)` | `9223372036854775807` | **`-1`** |
| `print(e == 9223372036854775807)` | `true` | **`false`** |
| `print(e + 0)` | `9223372036854775807` | **`-1`** |

## Why this is a DIFFERENT root cause from the interpolation defect

The sibling row's defect was in the scalar **renderers**: the value was intact
and only its text was wrong, and `print(x)` on a bare `i64` local was already
correct even before the fix. Here:

- the corruption survives a comparison (`==` is false), so it is not in any
  to-string path;
- the corruption survives arithmetic (`e + 0` is `-1`), so the stored bit
  pattern itself is wrong;
- an explicit `val e: i64 = arr[0]` annotation does not help, so it is not a
  type-inference miss at the read site.

Conclusion: the truncation happens when the value is **stored into or read back
out of the array**, before any consumer sees it. The `-1` / `0` signature is the
familiar `(value << 3) | TAG_INT` 61-bit payload loss (see
`stress_f02_i64_boxing_truncation_2026-07-17.md`), so the array element is being
held as a tagged `RuntimeValue` rather than a raw `i64` — but unlike the
renderer sites, here there is no bypass to add, because the loss happens in the
representation and not in a call. Fixing it means an `[i64]` array must store
raw 64-bit elements (or the box must be lossless), which is a representation
change, not a one-line routing change.

## Not yet isolated

The exact store/load site was not located. Start from the array-literal
construction and `lower_index_expr` in
`src/compiler_rust/compiler/src/mir/lower/`, and from `Value::Array` /
`RuntimeValue` array element handling in
`src/compiler_rust/runtime/src/value/`. Note the sibling comment already in
`lowering_expr_ops.rs` about ANY-typed element reads carrying "the raw tag-boxed
RuntimeValue bit pattern (`v << 3` for small ints)" — that is very likely the
same machinery, seen from the read side.

## Executable pins (deliberately RED)

Both are RED on exactly this defect and on nothing else; per
`.claude/rules/testing.md` a correct spec that fails is a legitimate artifact
and these assertions must not be weakened to make them green.

- `test/03_system/compiler/i64_interpolation_engine_parity_spec.spl` — the
  `agrees with the interpreter on a function-return i64 and an array element`
  example. `Results: 7 total, 6 passed, 1 failed`.
- `test/03_system/compiler/scalar_interpolation_engine_parity_sweep_spec.spl` —
  the byte-identical-lines and no-bare-`-1`/`0` examples.
  `Results: 4 total, 2 passed, 2 failed`.
- Fixture:
  `test/fixtures/repro/compiler/scalar_interpolation/scalar_interp_engine_parity_probe.spl`,
  line `I64_MAX_ARRELEM`.

Note both specs spawn subprocesses: `bin/simple test` is the tree-walk
interpreter and cannot reach the JIT at all, so an in-body assertion here would
be vacuous. They accept `SIMPLE_PARITY_BIN` to point at a binary other than the
deployed `bin/simple`.

## Unblock condition

An `[i64]` array element must round-trip a full 64-bit signed value under the
JIT: `arr[0] == i64::MAX` must be `true` and `arr[0] + 0` must equal `i64::MAX`.
When that holds, the two specs above go fully green with no edit.
