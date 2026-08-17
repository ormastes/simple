# Array `.at(i)` returns `nil` for EVERY index — all Option call sites take the None branch

**Date:** 2026-08-01
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
`compile --native`) FIXED to JIT parity** — see
`array_at_native_llvm_lane_2026-08-01.md`. The pure-Simple `native-build` lane
is still OPEN (no `at` arm in its MIR lowering; fails loudly).
**Severity:** CRITICAL on native — silent wrong answer, no error, no crash

### Lane table (all rows PROVED by transcript)

| Lane | How to select | Behaviour before fix | After fix |
|---|---|---|---|
| Rust-seed tree-walking interpreter | `SIMPLE_EXECUTION_MODE=interpret` | **loud** — `method 'at' not found on type 'array'` | correct Option |
| Rust-seed JIT (**the default** for `simple foo.spl`) | default | **silent `nil` for every index** | **correct Option** (11 examples 6 failures → 11/0) |
| Native LLVM (Rust seed) | `simple compile --native --backend llvm` | **silent absent for every index — now CONFIRMED by running a real ELF, no longer a prediction** | **correct** (`at(0)` ABSENT→PRESENT); parity with JIT |
| Native, pure-Simple | `simple native-build` | LOUD `unresolved method call: at` at MIR lowering | still OPEN — no `at` arm in the pure-Simple MIR lowering |
| Pure-Simple compiler's own interpreter | n/a — cannot self-host at HEAD | implements `at` (source read; **INFERRED**, not run) | — |

### JIT lane fix — what it actually took

The "map `at` to a runtime call" half was the easy part. Three separate defects
had to be fixed together before a single in-range read was correct, and each one
was only visible by rebuilding and RUNNING; none was reviewable:

1. **Dispatch (the reported cause).** `"char_at" | "at" => rt_string_char_at` in
   `codegen/instr/calls.rs` and `codegen/instr/closures_structs.rs` sent an array
   receiver down the *text* path. `at` now maps to a new receiver-dispatching
   `rt_at`, which tests the receiver and calls `rt_array_at` for arrays and
   `rt_string_char_at` otherwise. **Text `.at()` behaviour is unchanged** — it
   still yields a raw character, not an `Option`.

2. **Result typing — this one is why fixing only the dispatch is not enough.**
   `at` was missing from the array method return-type table in
   `hir/lower/expr/mod.rs`, so `xs.at(i)` typed as `TypeId::ANY`. `case Some(v)`
   desugars to an `rt_enum_payload` builtin whose HIR type gates whether MIR
   emits `UnboxInt`; with `ANY` no unbox was emitted and the binding stayed
   tag-boxed. Measured: `xs.at(0)` on `[10, …]` bound `v = 80` (10 << 3), and
   `at(3)` on `[0,1,2,3,4]` bound `24` (3 << 3). `at` now types as `T?`
   (`HirType::Pointer`), which is what `get_enum_variant_field_types_with_hint`
   needs to recover the element type.

3. **`case nil:` could not see a boxed `Option::None`.** `case nil` is a
   `Pattern::Literal(Expr::Nil)` and lowered to a raw `subject == nil`
   comparison, while `case None:` (a `Pattern::Enum`) already lowered to
   `rt_is_none`. A boxed `Option::None` is a heap object, never raw-equal to
   `nil`, so with the boxed representation the `nil` arm did not match — and
   since the `Some` arm did not match either, the whole `match` **fell through
   and bound nothing**, silently. `Pattern::Literal(Expr::Nil)` now also lowers
   to `rt_is_none`, so the two spellings agree on every representation.

### Why boxed `Option` and not the raw/flat form

`stmt_lowering.rs` supports two optional representations and picks between them
at runtime with `rt_enum_id(subj) >= 0`, deliberately passing a *raw* payload
through untouched — so a raw payload has to be an untagged `i64`. **The nil
sentinel is the untagged word 3**, so a raw optional holding the value 3 is
indistinguishable from absence by construction. `xs.at(3)` on `[0,1,2,3,4]` is
exactly that case, which is why the spec pins both index 3 and element value 3.
The boxed form has no collision: `Some(3)` is a heap object whose payload is the
tag-boxed `3 << 3` = 24, and absence is a distinct `Option::None` object.

This is the same "the two encodings are not interchangeable" trap recorded for
the interpreter fix, in its second form: there the seed needed a real
`Value::some`/`Value::none` rather than the pure-Simple flat encoding; here the
seed needed the *boxed* `Option` rather than the raw migration form. Both times
the wrong choice produced a silent no-match, not an error.

### Verification (JIT lane)

`simple test` CANNOT verify this lane: the test-runner apps are pinned to the
interpreter by `run_file_with_interpreter_mode`
(`driver/src/main.rs`), so a green spec run proves only the interpreter. The JIT
lane was verified with the same assertions run as a plain program (a bare
`simple foo.spl` selects the JIT), 11 checks mirroring
`test/01_unit/lib/common/array_at_option_spec.spl`:

```
unpatched seed (bin/release/.../simple.pre-segv-fix-20260731):  11 examples, 6 failures
patched seed:                                                   11 examples, 0 failures
```

Non-vacuity is exactly the 6: every failure was an in-range hit or the
index-3/value-3 case — the only assertions that distinguish "absent" from
"unimplemented". The 5 that passed unpatched (out-of-range, negative, empty)
passed *vacuously*, because an unimplemented `.at()` returns `nil` and `nil`
reads as absent. Both `case nil:` and `case None:` spellings were checked.

Regression-checked on the same binary: `text.at(i)` and `text.char_at(i)` keep
their raw-character results, `case nil` still matches a plain nil subject, still
does NOT match a non-nil value, non-nil literal patterns still work, and a
user-written `fn f() -> i64?` still matches `Some`/`None` correctly.

**Native LLVM remains OPEN and was NOT verified.** The remaining
`"char_at" | "at" => Some("rt_string_char_at")` mappings under
`codegen/llvm/**` (`functions/calls.rs`, `emitter.rs`, `functions.rs`) still
need the same `rt_at` redirect. They were deliberately left alone rather than
edited blind: this build was made without the `llvm` feature, so that lane could
not be run here, and the three defects above show that the dispatch edit alone
does not make a lane correct.

Two corrections to the first draft of this document, both worth stating because
they change what the bug *is*:

1. **`simple foo.spl` is the JIT lane, not the interpreter.** `should_prefer_interpreter_for_source`
   (`src/compiler_rust/driver/src/exec_core.rs:940`) only prefers the interpreter
   for `.shs`, for one hard-coded path, and for sources mentioning `std.cli` /
   `get_cli_args`. Everything else goes to the JIT with interpreter fallback. An
   unqualified "I ran it and got nil" therefore says nothing about the interpreter.
2. **The interpreter was never silent.** It raised a hard missing-method error.
   The silent-`nil` behaviour is specific to JIT and native. This matches the
   recorded pattern that the interpreter is frequently the *correct* lane, and it
   means the blast radius is the compiled lanes only.

## Symptom (PROVED)

On the JIT and native lanes, `arr.at(i)` returns `nil` for *every* index —
in-range hits included. It is not a bounds bug and not an off-by-one; the method
is simply not implemented for arrays, and the unhandled path yields `Nil`.

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
(the 154 MB LLVM-enabled seed; the live `bin/simple` has no `run`/`test`).
The left column is the **default (JIT)** lane, not the interpreter:

```
=== default / JIT ===            === native LLVM ===
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

Both compiled lanes agree, and both are wrong at indices 0..4.

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

The interpreter lane, by contrast, refuses the same program outright:

```
$ SIMPLE_EXECUTION_MODE=interpret simple at_flat.spl
len=5
idx  xs[i]      xs.at(i)
error: semantic: method `at` not found on type `array` (receiver value: [10, 20, 30, 40, 50])
```

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
earlier lane, in its live method-eval path:

- `src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl:833`

It uses the flat Option encoding (the element itself is `Some`, `nil` is
`None`, per `eval.spl match_pattern`) and bounds-checks `0 <= i < len`. That is
the semantics to mirror into the seed.

> **Path corrected 2026-08-01.** This originally read "in **both** of its
> method-eval paths" and also listed
> `interpreter/eval_methods.spl:300`. There was only ever **one** live path:
> `eval_methods.spl` was a dead duplicate shadowed by the `_EvalOps` package
> copies (sabotage-proven in both directions) and was deleted in
> `f97dfbbb8ee`. The conclusion is **unchanged** — the surviving `_EvalOps`
> copy is the one that carries the `at` arm, and it is a superset of the
> deleted one. Only the "both paths" redundancy claim was false. See
> `doc/08_tracking/bug/2026-08-01_interpreter_eval_text_method_duplicate_live_subset.md`.

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

## Fix — interpreter lane (LANDED)

`handle_array_methods` in
`src/compiler_rust/compiler/src/interpreter_method/collections.rs` gained an
`"at"` arm returning `Value::some(elem)` / `Value::none()`, with a **signed**
index so `at(-1)` is `None` rather than a wrap-around (the neighbouring `get`
arm uses `eval_arg_usize` and cannot express a negative index).

One thing to know before copying the pure-Simple implementation verbatim: the
two compilers use **different Option encodings**, and they are not
interchangeable.

- The pure-Simple interpreter uses a *flat* encoding — the bare element stands
  for `Some`, `nil` for `None` (documented at `eval.spl match_pattern`).
- The seed uses a *real* Option value, built with `Value::some` / `Value::none`.

Returning the bare element on the seed does not work: its pattern matcher
rejects a bare `i64` against `Some(v)`/`None` with
`invalid pattern: match expression exhausted without matching any pattern for
i64 value 10`. That was observed directly while developing this fix — it merely
trades a loud missing-method error for a loud missing-pattern one.

Verified against `test/01_unit/lib/common/array_at_option_spec.spl`:

```
unpatched seed:  11 examples, 11 failures
patched seed:    11 examples, 0 failures
```

Every failure on the unpatched side is `method 'at' not found on type 'array'`,
so the spec is non-vacuous on all eleven examples, including the in-range ones
that are the only assertions capable of distinguishing "absent" from
"unimplemented".

## Still OPEN — JIT and native LLVM

The compiled lanes are unchanged and still return `nil` for every index. Six
codegen sites map `at` to a *string* runtime call unconditionally, by name,
with no receiver-type test:

```
src/compiler_rust/compiler/src/codegen/instr/calls.rs:3235
src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1363
src/compiler_rust/compiler/src/codegen/llvm/emitter.rs:178
src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2371
src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:2097
```

Each must become receiver-type-aware and route an array receiver to a
bounds-checked Option accessor. Until then, **the default `simple foo.spl`
invocation still silently mis-executes every one of the ~161 call sites** — the
interpreter fix does not cover the lane most people actually run.

The pure-Simple compiler has the same shape of gap on its own native path:
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` handles
`char_at`, `index_of`, `substring`, dict `get`, etc., but has no `at` case, so
only its interpreter implements `.at()`.

Do **not** build any of this on `list.get(i)` — it is separately defective
(returns `value << 3`, tag-boxing defect, owned by another lane).

Do not blanket-rewrite the call sites. The call sites are overwhelmingly correct
already; it is the method that is missing. Fixing the method fixes the ~161
sites at once, and any bulk edit risks reverting sibling lanes' work. No call
site was edited for this fix, and none should be.

### Grep hazard while reproducing this census

The default `grep` on this box is **ugrep 7.5.0**, not GNU grep, and the two
disagree on `'"[^"]*\.at\('`: ugrep splits the 43 excluded in-string matches as
"2 js/engine + 41 in-string" while GNU grep (`/usr/bin/grep`) attributes all 43
to in-string. The totals above (341 / 298 / 114 / 184) were re-derived under
`/usr/bin/grep` and are identical either way, but any re-count should pin the
binary explicitly rather than trust `grep` on `PATH`.

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

Note that a spec run selects the **interpreter**, so a green spec is not
evidence about the native or JIT lanes — which is exactly why
`test/01_unit/lib/common/array_at_option_spec.spl` passing today does **not**
close this bug. Native must be verified by `simple compile --native` plus
running the produced binary, and JIT by a default `simple foo.spl` run, as done
in the transcripts above.


## Adjacent finding 2026-08-17 (P0-core silent-wrong lane): `.at()` RETURN SHAPE diverges between engines

Not the defect this doc tracks — the filed defect (`at` returning nil for every
index, and the missing `at` arm in pure-Simple MIR lowering) was NOT reproduced
and NOT re-tested on the native lane. But the probe written to check it exposed
a different divergence in the same method, on the two engines this tree actually
ships:

```
val a: [i64] = [10, 20, 30]
print a.at(1)
```

| engine | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter` | `20` |
| `SIMPLE_EXECUTION_MODE=jit`         | `<enum@0x46988592660>` |

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59,536,728 bytes, mtime
2026-08-16 22:59:37 UTC (Rust seed). Exit 0 both times, no diagnostic.

The JIT result is the *defensible* one if `at` is specified to return `T?` — it
is handing back the Option enum unopened. The interpreter is silently unwrapping
it. Whichever is intended, they cannot both be, and today the same source text
yields a number on one engine and an enum handle on the other. Anything that
pattern-matches the result works on one engine and falls through on the other;
anything that prints it produces either a value or a pointer.

Filed here rather than as a new doc because it is the same method and a reader
of this doc needs to know it; if the owner disagrees it should be split out.
Not investigated: which behaviour is specified, where the unwrap happens, and
whether `.get()`/`.first()`/`.last()` share it.
