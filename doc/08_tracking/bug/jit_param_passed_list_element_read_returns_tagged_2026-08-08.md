# JIT: element read from a parameter-passed untyped `list` returns the TAGGED value (`v << 3`)

**Filed:** 2026-08-08 · **Severity:** critical (silent wrong data, no diagnostic,
source reads correct) · **Engine:** JIT (Cranelift) via `bin/simple run` on the
Rust **seed** binary `bin/release/x86_64-unknown-linux-gnu/simple`
**Interpreter (`SIMPLE_EXECUTION_MODE=interpret`, `bin/simple test`): CORRECT on
every variant below.**

## Summary

Inside a function whose parameter is declared as an untyped `list` (or is
untyped entirely), an element read `data[i]` yields the value **still carrying
its small-int tag** — numerically `v << 3`, i.e. `v * 8`. The same expression
written inline in `main`, or reading a list *constructed locally inside the same
function*, is correct. A parameter typed `[i64]` is correct.

The value prints correctly (`to_text` / interpolation untag it) and compares
correctly against small literals, so it survives both source review and casual
`print` debugging. It is wrong the moment it meets **arithmetic against another
variable**.

## Minimal reproduction

```simple
fn f_list(data: list) -> i64:
    100 - data[3]

fn f_i64(data: [i64]) -> i64:
    100 - data[3]

fn main():
    var d = []
    d.append(1)
    d.append(2)
    d.append(2)
    d.append(2)
    val xm = d[3]
    print("main inline : {100 - xm}")   # 98  CORRECT
    print("f_list      : {f_list(d)}")  # 84  WRONG  (100 - 16, and 16 == 2<<3)
    print("f_i64       : {f_i64(d)}")   # 98  CORRECT
```

## Variant matrix (`bin/simple run`, element value = 2, expression `100 - x`)

| form | result | verdict |
|------|--------|---------|
| inline in `main`, `val x = d[3]` | 98 | correct |
| inline in `main`, `100 - d[3]` | 98 | correct |
| list built **locally inside** the fn | 98 | correct |
| param `data: list`, `val x = data[3]` | **84** | tagged (`2<<3` = 16) |
| param `data: list`, `100 - data[3]` | **84** | tagged |
| param untyped `data` | **84** | tagged |
| `list` as the **second** param | **84** | tagged (not a first-arg/self issue) |
| param `data: list` passed on to another fn | **84** | tagged, propagates |
| param `data: [i64]` | 98 | correct |
| param `data: list`, `data.at(3)` | **-4379365875421** | unrelated garbage (raw word) |

Every row is correct under the interpreter.

## Why it hides from review — the generalizable lesson

With the true value 2 held as 16:

| expression | evaluates | happens to be |
|------------|-----------|---------------|
| `"{padding_len}"` | `"2"` | **right** (interpolation untags) |
| `padding_len <= 0` | false | **right** by luck |
| `padding_len > 255` | false | **right** by luck |
| `padding_len > data_len` (4) | **true** | wrong |
| `data_len - padding_len` | **-12** | wrong |

**Comparison against a literal can be accidentally correct; arithmetic against
another variable is not.** That asymmetry is exactly why source review passed
and why a `print` of the variable reinforced the wrong conclusion.

## The two field sightings — SAME root cause (demonstrated, not inferred)

**Sighting A — list→hex helper returns `v*8 & 0xFF` per byte.** Reproduced:

```simple
fn helper_hex(data: list) -> text:   # nibbles via data[i] / 16 and data[i] % 16
```

For `[1, 2, 16, 255]` the inline loop gives `010210ff`; the byte-identical
helper gives `0810808`. The helper's `v / 16` sees `v*8`, so the digits are
scaled by 8. This is the defect that produced the fabricated hex constants
corrected in `3fa1f1dcccf`.

**Sighting B — `src/lib/common/aes/padding.spl` `pkcs7_unpad` never strips.**
Reproduced. `data: list`, so `padding_len` = 16 instead of 2, so
`padding_len > data_len` is true and the function early-returns its input for
**valid** padding. Nothing was wrong with that source's control flow.

## Relation to the known shift-left-3 family

Same family, **new trigger**. Existing records —
`any_receiver_element_read_shift_and_tag_2026-08-06.md` (element read off an
`any` receiver), the filed `list.get returns value shifted left 3`, and the
`rt_value_as_int` returning `value >> 3` history — all concern erased/`any`
receivers or `.get`. This one fires on a **plainly declared `list` parameter**
with ordinary `a[i]` indexing, which is far more common in existing code and
carries no visible erasure cue. Treat as a sibling, not a duplicate.

## Ruled out

- **Builtin name collision.** `pkcs7_unpad` appears nowhere in
  `src/compiler_rust/**/*.rs`. (`to_hex` does exist as a builtin method, but the
  reproduction above uses no such name and still fails.)
- **Stdlib-bundling / edit-visibility.** The reproduction is a standalone file
  with no `use`, so no stdlib copy is in the path.
- **The `?` / early-return family.** `early()` with a dead `if false: return`
  and a locally built list returns correctly.
- **Source error in `pkcs7_unpad`'s control flow.** It is correct as written;
  the separate security defect below is about its *contract*, not this bug.

## NOT tested

The pure-Simple codegen. `bin/simple` is the **Rust seed** (prints the seed
banner), so everything here is the seed's JIT lowering. Disk is at 96%, so no
bootstrap build was possible to check whether the pure-Simple compiler shares
the defect. **No seed fix is attempted** — it would need a rebuild, and the
shared deployed binary must not be redeployed.

## Impact

This defeats source review as a means of establishing behavior for any function
taking an untyped `list` and doing arithmetic on its elements. Conclusions
reached today by inspection over such code should be re-examined empirically.
Note also that `bin/simple test` **cannot** catch it: the spec suite runs the
interpreter, which is correct here, so affected code stays green.

## Workaround

Declare element types: `[i64]` / `[u8]` parameters read correctly. Applied to
`src/lib/common/aes/padding.spl` in this change, with a comment stating it is a
workaround and not a fix.

## Unblock condition

`bin/simple run` returns 98 for the `f_list` row of the matrix above.

## Measurement trap hit while verifying this (worth its own note)

`bin/simple run` resolves `use std.*` **relative to the current working
directory**. Run from a scratch dir with no `src/lib/`, it does not error — it
silently serves a **bundled** stdlib. A verification run of the fixed
`pkcs7_unpad` from `/tmp/.../scratchpad` printed the OLD fail-open result
(`[1, 2, 2, 2]`), which would have been read as "the fix didn't work". The same
probe from the repo root printed `[1, 2]`.

The tell was a *sibling* probe: importing a deliberately added
`__sabotage_probe_marker` reported `module
'<scratchpad>/src/lib/common/aes/padding.spl' does not provide it` — naming a
path that does not exist, while the neighbouring import of the same module had
just "succeeded". **Always run the sabotage probe from the same cwd as the
measurement**, and confirm the marker is visible before believing any stdlib
result. From the repo root the marker returned 4242, and the fixed module then
verified correctly on the JIT lane (valid padding stripped, invalid rejected).
