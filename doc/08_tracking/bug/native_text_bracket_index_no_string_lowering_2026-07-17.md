# Native path: `text[i]` bracket indexing has no string-aware lowering — garbage output, then SIGSEGV on comparison

**Date:** 2026-07-17
**Severity:** Critical (silent wrong output escalating to crash; core string/codepoint-indexing feature)
**Status:** open
**Task:** #178 native text interpolation + string ops verification round 2 (lane S47)

## Symptom

`s.char_at(i)` (method call) works correctly natively and matches the oracle.
`s[i]` (bracket-index syntax on the same receiver, same semantics per the
codepoint-indexing rule from bug #39: `len()` is bytes, `text[i]` is
codepoint) does **not** — it silently returns a garbage 64-bit integer when
printed, and **crashes with SIGSEGV** when the result is used in an equality
comparison.

## Root cause (found via code read, `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` `case Index(base, index):`, ~line 1622)

The `Index` HIR-expr lowering handles exactly three receiver shapes:

1. `Range` index (`a[1:3]`) — explicitly rejected with a loud build error
   (existing, unrelated fix).
2. Runtime **dict** receiver — routes to `rt_dict_get`.
3. Runtime **array** receiver (`local_is_runtime_array`) — routes to
   `rt_array_get`.
4. **Everything else** (the `else` branch, line 1736-1745) — falls through to
   a raw `emit_gep` + `emit_load`, treating the base local as a flat pointer
   to `result_type`-sized elements and loading at the raw `index` offset.

There is **no case for a `text`/string receiver**. A string in this runtime is
represented as a tagged heap-string handle (see the many `ensure_tagged_str`
/ `rt_string_new` / `rt_interp_cstr` references throughout
`method_calls_literals.spl`), not a raw pointer to codepoint-sized elements.
`s[i]` therefore falls into branch 4: it GEPs into the *tagged handle value
itself* as if it were a flat i64 array and loads 8 bytes from the wrong
address, producing a meaningless 64-bit integer. `.char_at()`, by contrast,
has its own dedicated handling (`method_calls_literals.spl` ~line 1634) that
correctly resolves to a real runtime string-character accessor — this is why
`char_at()` works but `[]` does not.

## Repro 1 — wrong value, no error, in interpolation

```simple
fn main():
    val s = "café"
    print "L2:{s[0]}|END"
    print "L3:{s[3]}|END"
```

- Oracle: `L2:c|END` ... `L3:é|END`
- Native: `L2:729127739747|ENDL3:1808504898734497695|END` (garbage, varies run to
  run/build to build)

`s.char_at(1)` in the same file correctly prints `e` on both paths (control,
proving the receiver/string itself is fine).

## Repro 2 — SIGSEGV on comparison

```simple
fn main():
    val s = "hello"
    val c = s[1]
    if c == "e":
        print "MATCH|END"
    else:
        print "NOMATCH|END"
```

Native run:
```
[simple-runtime] Fatal: SIGSEGV at address (nil)
```
(Oracle prints `MATCH|END`.)

Isolated further: `print(c)` alone (no comparison) does **not** crash — it
just prints the garbage integer (e.g. `4755865198328300622`), confirming the
crash is triggered specifically when the mistyped result is fed into a
string-equality comparison that dereferences it as if it were a real tagged
string pointer.

## Expected

`s[i]` must lower identically to `s.char_at(i)` for a string receiver:
codepoint-indexed, bounds-checked, returning a proper tagged single-character
string — not fall through to the generic raw-array GEP/load path used for
untyped/unresolved receivers.

## Suggested direction

Add a string-receiver branch to the `Index` case in `expr_dispatch.spl`,
parallel to the existing dict/array branches: detect a string receiver (via
`self.local_is_str(base_local)` — already used elsewhere in this file, e.g.
the `.len()` field-access special-case at line 427) and route to the same
runtime call `char_at()` uses (`method_calls_literals.spl` ~line 1634), rather
than reaching the raw-pointer `emit_gep`/`emit_load` fallback.

## Verification

- Reproduced on worktree `/home/ormastes/dev/wt_r_find_infer` at tip
  `ffc0c360ba4` (fetched 2026-07-17), using
  `env -u SIMPLE_BOOTSTRAP bin/simple run` (oracle) and
  `env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple native-build`
  (native).
- `.char_at()` on the identical receiver/index is confirmed correct on both
  paths in the same probe file, isolating the defect to bracket-index syntax
  specifically.
