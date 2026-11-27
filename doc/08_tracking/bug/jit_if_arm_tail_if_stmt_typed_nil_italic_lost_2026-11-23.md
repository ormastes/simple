# Seed JIT: an `if` arm ending in an `if`/`else` statement is typed NIL (italic text painted upright)

- **Date:** 2026-11-23
- **Severity:** P2 (silent wrong value)
- **Status:** FIXED 2026-11-23 (seed HIR `lower_do_block`)
- **Area:** `src/compiler_rust/compiler/src/hir/lower/expr/control.rs`

## Symptom

The web catalog `html` page at 1x: the JIT output (`SIMPLE_EXECUTION_MODE=jit`)
differed from the interpreter in 4482 bytes, in two text runs: `<address>Simple
renderer team</address>` and `<var>frame_time</var>`. The interpreter painted
them italic. The JIT painted them upright. Every italic run was affected (`<i>`,
`<var>`, `style="font-style:italic"`).

`browser_font_family_for_style("sans-serif", false, true)`
(`src/lib/nogc_sync_mut/text_layout/font_provider.spl`):

| engine | result |
|---|---|
| interpreter | `__simple_font_face__\|/usr/share/fonts/truetype/liberation/LiberationSans-Italic.ttf\|sans-serif` |
| jit (base) | `__simple_font_face__\|1582642081\|sans-serif` |

The face path became a number that changes from run to run. Font lookup then
fell back to the regular face.

## Minimal repro

```simple
fn a_faces() -> [text]:
    ["/a/A.ttf"]
fn b_faces() -> [text]:
    ["/b/B.ttf"]

fn p4(cat: text, bold: bool) -> text:
    val faces = if cat == "sans":
        if bold: a_faces() else: b_faces()
    else:
        []
    "p4|" + faces[0]
```

Results: the interpreter returns `p4|/b/B.ttf`; the JIT on base returns
`p4|201832897`. The following shapes were correct on base:
- the same function with `else: a_faces()`;
- the arm without nesting (`if c: b_faces() else: []`).

## Root cause

The parser makes the multiline arm a `DoBlock([Node::If(..)])`, which is an
`if` STATEMENT, not an expression. `lower_do_block` only took a result type from
`Node::Expression` / `Node::Return`, so the arm was typed `NIL`. MIR
`lower_block_expr` still yields the tail statement's value, which is why the
pointer reaches the merge.

`lower_if`'s join then treated the NIL arm as bottom (`hir_arm_is_bottom`) and
took the `else` arm's type. That arm was `[]` with its configured default
element type `i32`. The empty-literal contextualisation could not help, because
its sibling type was NIL rather than an array. So `faces: [i32]`, and
`faces[0]` was emitted as `rt_array_get` + `UnboxInt` + `UnitNarrow 64->32` on
a text pointer.

## Fix

`lower_do_block` now types a block whose LAST statement is an `if`/`else`
statement from that statement's arms (`hir_tail_if_value_type`). It takes the
first arm whose tail value is neither bottom nor an empty `[]` literal,
recursing through nested tail `if`s. An `if` without `else` keeps NIL.

## Evidence

- `src/compiler_rust/compiler/tests/if_arm_tail_if_type_jit.rs`:
  - base: 2 of 3 FAIL (left 100, right 111);
  - fixed: 3/3 pass.
- Catalog JIT vs interpreter byte comparison: see the lane report (`html` 1x
  4482 -> 0 differing bytes).
