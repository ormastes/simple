# Array `.at(i)` returns `nil` for EVERY index — all Option call sites take the None branch

**Date:** 2026-08-01
**Status:** OPEN (census + reproduction complete; fix not landed)
**Severity:** CRITICAL — silent wrong answer, no error, no crash
**Lanes affected:** Rust-seed tree-walking interpreter AND native LLVM (PROVED).
JIT not separately reachable via a CLI flag on the deployed seed.
**Lane NOT affected:** the pure-Simple compiler's own interpreter
(`src/compiler/10.frontend/core/interpreter/`) already implements it correctly.

## Symptom (PROVED)

`arr.at(i)` on an array returns `nil` for *every* index — in-range hits included.
It is not a bounds bug and not an off-by-one; the method is simply not
implemented for arrays, and the unhandled-method path yields `Nil`.

Probe (`/dev/shm/fable-atopt/probe/at_flat.spl`):

```simple
fn main():
    val xs: [i64] = [10, 20, 30, 40, 50]
    print("len=" + xs.len().to_text())
    var i = 0
    while i < 7:
        val direct = if i < xs.len(): xs[i] else: -999
        val a = xs.at(i)
        print(i.to_text() + "    " + direct.to_text() + "        " + a.to_text())
        i = i + 1
    print("at(-1) = " + xs.at(-1).to_text())
    val e: [i64] = []
    print("empty at(0) = " + e.at(0).to_text())
```

Run with `bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`
(the 154 MB LLVM-enabled seed; the live `bin/simple` has no `run`/`test`):

```
=== interpreter ===              === native LLVM ===
len=5                            len=5
idx  xs[i]      xs.at(i)         idx  xs[i]      xs.at(i)
0    10        nil               0    10        nil
1    20        nil               1    20        nil
2    30        nil               2    30        nil
3    40        nil               3    40        nil
4    50        nil               4    50        nil
5    -999      nil               5    -999      nil
6    -999      nil               6    -999      nil
at(-1) = nil                     at(-1) = nil
empty at(0) = nil                empty at(0) = nil
```

Both lanes agree, and both are wrong at indices 0..4.

A `match` probe confirms the Option-shaped consequence directly — with a
5-element array, **every** arm resolves to `None`:

```
at(0) None
at(3) None
at(4) None
at(5) None  <-- OOB correct
at(-1) None <-- neg correct
empty at(0) None <-- correct
```

Because the failure mode is `None`, and `None` is exactly what an out-of-range
read *should* produce, every call site degrades to its "absent" branch silently.
There is no error, no crash, and no log line. Only the three genuinely-absent
rows are right, and they are right by accident.

## Root cause

`src/compiler_rust/compiler/src/interpreter_method/collections.rs`,
`handle_array_methods` — the `match method { ... }` has arms for `len`,
`length`, `ndim`, `is_empty`, `first`, `last`, `get`, `has`, `contains`,
`push`, `append`, ... and **no `"at"` arm**. It falls to `_ => return Ok(None)`
("not handled"), and the caller substitutes `Value::Nil`.

The only `at` binding anywhere in the seed is for **text**, not arrays:

- `src/compiler_rust/compiler/src/interpreter_method/string.rs:368` — `"char_at" | "at" =>`
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs:3235` — `"char_at" | "at" => Some("rt_string_char_at")`
- `src/compiler_rust/compiler/src/codegen/llvm/emitter.rs:178` — same
- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2371` — same
- `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:2097` — same
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1363` — same

So `text.at(i)` works (it is `char_at`); `array.at(i)` does not exist.

The pure-Simple compiler already has the correct implementation, added by an
earlier lane, in both of its method-eval paths:

- `src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl:833`
- `src/compiler/10.frontend/core/interpreter/eval_methods.spl:300`

Both use the flat Option encoding (the element itself is `Some`, `nil` is
`None`, per `eval.spl match_pattern`) and bounds-check `0 <= i < len`. That is
the semantics to mirror into the seed.

## Census — CORRECTS the previously recorded figure

The recorded claim was **"~325 `.at()` call sites, ~253 expect `Option<T>`"**.
Re-measured at base `f7bfaf973de2a2c398fec7f11ea4235e19f557ab`; both numbers are
**too high**. Corrected breakdown:

| Class | Lines | Notes |
|---|---:|---|
| Raw `\.at(` matches in tracked `*.spl` | **341** | starting point |
| — JS-engine implementation files (`*/js/engine/*`) | −2 | JS `Array.prototype.at`, unrelated language |
| — `.at(` appearing *inside a string literal* | −41 | JS source snippets under test, e.g. `test/01_unit/lib/common/web` |
| **Real Simple `.at(` call sites** | **298** | |
| — static constructor `Type.at(...)` | −114 | user-defined `static fn at`, NOT element access |
| — user-defined instance `fn at` | −16 | `ray.spl` `self.at(t)`, `search/types.spl` `fn at(i) -> Id` |
| **True container element access** | **~168** | |
| of which provably Option-consuming | **~161** | |

The 114 static-constructor sites are real, defined methods and are completely
unrelated to container indexing:

```
src/compiler/00.common/diagnostics/label.spl:18:    static fn at(line, column, message) -> Label
src/compiler/00.common/diagnostics/span.spl:23:    static fn at(pos, line, col) -> Span
src/lib/common/sdn/value.spl:15:                     static fn at(line, column) -> Span
src/lib/common/search/types.spl:145:                 static fn at(index) -> MatchPos
src/lib/nogc_async_mut/debug/coordinator.spl:62:     static fn at(file, line, function_name) -> LocationInfo
```

plus `SourceLocation.at`, `ParseError.at`, `TemplateError.at`, `PixelSample.at`
in specs. The earlier "~325 / ~253" figure evidently swept these in along with
the 41 in-string JS snippets.

### How the ~168 container sites consume the result

Classified by what the caller actually does (window of 8 lines after the call):

| Consumption | Sites |
|---|---:|
| inline `match`/`case` or `.unwrap()` on the call line | 51 |
| assigned to a var that is then `match`ed / `unwrap`ed / nil-compared | 108 |
| assigned but not Option-consumed | 5 (3 are `ray.spl` `self.at(t)`, a user-defined method) |
| argument/return position, no assignment | 20 (13 are `types_spec.spl` `r.at(N)` → user `fn at(i) -> Id`) |

So **~161 of ~168 container sites (96%) expect `Option<T>`** — the *direction*
of the recorded claim is confirmed even though the magnitude was wrong.

Representative shapes:

```simple
# src/lib/skia/feature/glyph/ot_parser_gvar.spl:481
val p = match peak.at(i):
    Some(value): value
    None: return 0.0

# src/lib/skia/feature/stroke/expand.spl:254
val first_opt = cur_chords.at(0)
val last_opt  = cur_chords.at(cur_chords.length() - 1)
match first_opt: ...

# src/lib/skia/feature/color_management/tone_map.spl:384
if val Some(r) = m.at(row):
    if val Some(v) = r.at(col):
```

### Concentration

`.at()` is not evenly spread — it is dominated by the skia stack, which is where
the silent-`None` damage lands:

```
 38  src/lib/skia/feature/stroke/expand.spl
 19  src/lib/skia/feature/color_management/icc_writer.spl
 17  test/01_unit/lib/skia/ot_parser_spec.spl
 15  src/lib/skia/feature/stroke/dash.spl
 15  src/lib/skia/feature/path_effect/corner_discrete.spl
 13  test/01_unit/lib/common/search/types_spec.spl
 10  src/lib/skia/feature/glyph/ot_parser_gvar.spl
  9  src/lib/skia/feature/color_management/icc_profile.spl
```

Note `test/unit/**` and `test/01_unit/**` are parallel real directories (not
symlinks), so mirrored spec files are counted twice above; deduping the mirrors
gives 266 real sites instead of 298. The container/constructor split is
unaffected.

### Prior art in-tree

Two comments already record a partial version of this finding, from a lane that
worked around it rather than fixing it:

```
src/lib/common/jwt/encode.spl:266
  # Index access, not `.at()`: `.at()` is not a valid array/list method
src/lib/common/jwt/encode.spl:269
  # original `.at()` calls here would themselves error out
```

The comment's conclusion ("would error out") is wrong in an important way: it
does **not** error out, it silently returns `nil`. That is why the other ~161
sites were never noticed.

## Why this is worse than a crash

The nil-for-everything behaviour is indistinguishable from a legitimately empty
container. In `expand.spl` the stroke expander asks for the first and last chord
of a contour and gets `None` for both, so `closed` stays `false` and the contour
is treated as open — geometry silently changes rather than failing. In
`ot_parser_gvar.spl:481` the `None` arm is `return 0.0`, so variable-font delta
interpolation silently returns zero and the glyph renders at its default master.

This matches a family of defects already recorded for this repo (silent
pattern/dispatch mismatch): a `case`/`match` arm existing is not evidence it ever
runs, and `None` being *reachable* is not evidence `Some` is.

## Fix direction

Mirror the pure-Simple semantics into the seed:

1. `interpreter_method/collections.rs` `handle_array_methods` — add an `"at"`
   arm: `let idx = eval_arg_i64(...); if 0 <= idx < arr.len() { arr[idx].clone() } else { Value::Nil }`.
   Note the index must be read as **signed** and negative rejected — the existing
   `get` arm uses `eval_arg_usize`, which cannot express `at(-1)`.
2. The five codegen sites that map `"char_at" | "at" => rt_string_char_at` must
   become receiver-type-aware, or arrays will keep silently missing on native.
   Today they map `at` to a *string* runtime call unconditionally by name.
3. Do **not** build on `list.get(i)` — it is separately defective (returns
   `value << 3`, tag-boxing defect, owned by another lane).

Do not blanket-rewrite the call sites. The call sites are overwhelmingly correct
already; it is the method that is missing. Fixing the method fixes the ~161
sites at once, and any bulk edit risks reverting sibling lanes' work.

### Sentinel note

The nil sentinel is `3`, which is known to corrupt `??` on a raw `i64` at index
3. The flat Option encoding used by the pure-Simple implementation (element
itself is `Some`, `nil` is `None`) therefore has a latent collision for an
`[i64]` whose element value *is* the nil sentinel. The probe above covers index
3 specifically; a value-3 *element* is a distinct case and is not yet covered.

## Verification bar for the fix

Specs must cover, per container type: in-range hit, out-of-range, empty
container, index 3 (sentinel), and the boundary index `len-1` / `len`. Each must
be shown RED against the unpatched build first — trivially satisfiable today,
since every in-range read currently returns `None`.

Note that `bin/simple_seed test` runs the **interpreter**, so a green spec is
not evidence about the native or JIT lanes. Native must be verified by
`simple compile --native` + running the produced binary, as done above.
