# `[v; n]` with a non-literal fill and a computed count yields wrong values (default mode)

- Status: fixed on `release/1.0.0` by `74454b58b2fd` (2026-11-21); verified 2026-11-24 at `4da62cc1731`
- Found: 2026-11-24, web-render lcdround lane (`sfnt_glyf.spl` Skia AAA port)
- Binary: `/home/yoon/.cache/cargo-target-webrender-blend/release/simple` (seed, default execution mode)

## Repro

```
fn f(full: i64, len: i64) -> [i64]:
    var al: [i64] = [full; len + 1]
    al
fn h(full: i64) -> [i64]:
    val al: [i64] = [full; 3]
    al
fn main():
    val x: i64 = 64
    val a: [i64] = [x; 3]
    print("{a} {f(64, 2)} {h(64)} {f(5, 2)} {f(300, 2)}")
main()
```

| mode | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter` | `[64, 64, 64] [64, 64, 64] [64, 64, 64] [5, 5, 5] [300, 300, 300]` (correct) |
| default | `[64, 64, 64] [8, 8, 8] [64, 64, 64] [<value:0x5>, <value:0x5>, <value:0x5>] [<value:0x12c>, ...]` |

A literal count (`[full; 3]`) or a local fill (`[x; 3]`) is correct. A
parameter fill with a computed count (`[full; len + 1]`, also `[full; n]`
with `n` a parameter) stores the fill untagged: 64 reads back as 8 (64 >> 3),
small values print as raw `<value:0x..>`.

## Workaround in tree

`_aaa_trap_row_general` in `src/lib/common/encoding/sfnt_glyf.spl` allocates
`[0; len + 1]` and fills by loop (it accumulates the subtracted coverage from
zero), so it does not depend on this.

## Fix direction

Array-repeat lowering for a non-constant count must tag the fill value the
same way the constant-count path does.

## Resolution (2026-11-24, lane `work/compiler-chain-repeat-bugs-20261124`)

The repro binary was stale. It was built 2026-11-19, before
`74454b58b2fd` (2026-11-21). That commit made `lower_array_repeat_expr`
(`mir/lower/lowering_expr_collection.rs`) box the fill through
`box_value_as_runtime` before `rt_array_repeat`. Earlier, the raw fill
register went straight into the call. That is why 64 read back as 8 and 5 printed as
`<value:0x5>`. The constant-count path never had the problem because it
unrolls to a literal whose elements are boxed one by one.

On base `4da62cc1731` the repro prints the interpreter's answer in every mode.
f64, bool, i32, u8, text and i64 parameter fills with a computed count all
agree between the interpreter and the JIT/default mode.

Regression test: `src/compiler_rust/compiler/tests/float_chain_repeat_engines.rs`
(fixture `test/fixtures/native/float_chain_repeat/main.spl`, bits 512/1024/2048)
on the interpreter, the JIT and a native cranelift build. Red proof: replacing the
boxed `value_reg` with `raw_value_reg` makes the JIT and native report mask 512.

The `sfnt_glyf.spl` zero-fill workaround can stay or go. It does not depend on
the bug, and a binary rebuilt from `release/1.0.0` handles `[full; len + 1]` correctly.
