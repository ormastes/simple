# native lane: a `text` element is DESTROYED at the STORE, not lost at the read

- Status: PARTIALLY FIXED. `a[i]`, `.first()`/`.last()` and `for x in a` are
  fixed for all four element types. **Nested `[[text]]` / `[[bool]]` remain
  BROKEN** and the gate is deliberately left RED for them (root cause measured,
  see "Still open" below).
- Gate: `scripts/check/check-native-array-element-type.shs` — widened
  2026-08-24 from 4 cases (one access path) to **20** (4 element types x 5
  access paths: `index`, `first`, `last`, `for`, `nested`).
  - origin/main `16383395b5a`: `FAIL — 20 case(s) checked, 8 diverged:
    text/first text/last text/nested bool/first bool/last bool/nested
    f64/first f64/last`
  - now: `FAIL — 20 case(s) checked, 2 diverged: text/nested bool/nested`
  - The gate is NOT wired into any pre-push hook, precisely because it is
    honestly red. Promote it once nested is fixed.
- Lane: `native-build --backend=cranelift`, x86_64-unknown-linux-gnu. Interpreter
  was always correct.

## Symptom

```
fn main():
    var a: [text] = []
    a.push("ABCDEFGHIJ")
    print "S={a[0]}"      # native: RTS\001   interp: ABCDEFGHIJ
```

`[i64]` was correct, `[text]` printed a raw word, `[bool]` printed `1`/`0`,
`[f64]` failed to BUILD. `.len()` on the array stayed correct.

## Root cause (three independent gaps)

### 1. The STORE destroys the text (the real one)

`box_runtime_value` (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`)
guards against double-boxing with the STATIC predicate `is_tagged_text_local`.
That predicate does not hold for every text local that is already a TAGGED
handle at runtime — a plain `a.push("LITERAL")` on a `[text]` reaches the
boxing arm unmarked. `rt_strlen` is not tag-aware, so it read the tagged handle
as a raw `char*` and returned `strlen(header + 1)`, and `rt_string_new` then
COPIED those header bytes as the element's content.

Measured with gdb on the built binary:

```
Breakpoint 1, rt_interp_cstr ()
IN=0x5555555ddb71                       # tagged handle, TAG_HEAP = 1
0x5555555ddb70: 0x31 0x52 0x54 0x53     # RtCoreString.kind == RT_VALUE_HEAP_STRING
                                        # (0x53545231, bytes "1RTS")
OUT=0x5555555ddb80                      # header + 16 == s->data -- the decode
0x5555555ddb80: "RTS\001"               # ... and the CONTENT is the header bytes
```

So the read side was innocent: `rt_interp_cstr` returned a perfectly valid,
registered `RtCoreString`. Its *content* had already been replaced with the
`kind` magic bytes read from offset 1 plus the `reserved` flag byte, at push
time. That is why `a[i]`, `.first()` AND `for x in a` were all wrong at once.

Fix: normalize through `rt_interp_cstr` — the existing representation
AUTODETECTOR, already used for exactly this on the read side — before
`rt_strlen`/`rt_string_new`, making the store idempotent for both
representations without requiring the static marking to be complete.

**Trap for the next reader:** `a[0].len()` returned **4** on the broken build
and looked like proof the element was intact. It was `strlen("RTS\001")`. Use a
string longer than 4 characters and `od -c`; a 10-character string returned
`L=4`.

### 2. The READ discards the declared element type

`lower_index_expr` consults the base's MIR type FIRST. A container born from an
empty `[]` literal (`var a: [text] = []`) carries the ERASED `Array(i64)` MIR
type, so `result_type_from_base` was set true with a bogus `i64` element type,
which then BLOCKED the declared-HIR-element-type fallback entirely. Now a
base-derived `i64` is treated as "not yet known". No-op for a genuine `[i64]` —
which is exactly why `[i64]` was the one case that always worked.

### 3. `[f64]` failed the cranelift verifier

`rt_value_float`'s C parameter is a `double` and MIR correctly passes the
double, but `cranelift_codegen_adapter.spl` had no case for it, so the call fell
through to the all-i64 runtime import: cranelift declared `rt_value_float(i64)`
and rejected the function with
`inst18 (v14 = call fn1(v13)): arg 0 (v13) has type f64, expected i64`.
Every `[f64]` element store therefore failed to BUILD. Added the `f64 -> i64`
case, mirroring `rt_raw_f64_to_string`. Do NOT bitcast to i64 at the call site —
that is the %rdi/%xmm0 register mismatch `5fc2a871e35` fixed.

## Why it mattered beyond formatting

`CompileContext.error_message_at` returns `self.errors[index]` from a `[text]`.
Reduced to a fixture with the same shape (class field `[text]`, `push`, index
read through a method):

```
before: E=RTS\001
after:  E=expected type annotation
```

A Stage-2-compiled compiler was therefore destroying every diagnostic it had
correctly detected, before reporting it.

## Falsified premise from the previous lane

The prior recipe stated that `.first()`/`.last()` decode correctly and should be
copied as the model. They do not — they were reading the same destroyed data.
Measured on the same fixture at origin/main and after the fix, `.first()` and
`for x in a` still print a raw tagged handle as an integer: their read paths do
not decode at all. **Still open** (tracked below); the fix above only repairs
what they read, not how they read it.

## Round 2 (2026-08-24): the residual paths were READ-side, and not one defect

The store fix above repaired WHAT was read. It did not repair HOW the other
paths read it. Measured on the fixed build, `[text]`, one array, one push:

```
a[0]                -> ABCDEFGHIJ        (fixed in round 1)
a.first() ?? d      -> 103104798067584   raw tagged handle rendered as an int
for s in a: "{s}"   -> 110173329386353   same
n[0][0]             -> 105218053549009   same
```

**The decisive measurement — and the reason none of this is a data defect:**
inside the broken `for` loop, `s.len()` returned the CORRECT **10** while
`"{s}"` printed a pointer, and `s + "!"` concatenated onto the pointer. The
element was a perfectly good tagged heap string the whole time. Every residual
failure is an element-TYPE propagation gap, never a corrupted value. `[i64]` was
correct on every path throughout, which is the control.

Three independent sites, all reached by the same question ("does this local end
up satisfying `local_is_str`, so `coerce_concat_operand` passes it through
instead of calling `rt_raw_i64_to_string`?"):

### A. `for x in a` — FIXED (`mir_lowering_stmts.spl`, `lower_for`)

Two element-type sources were consulted in the WRONG ORDER and the second
clobbered the first unconditionally: the declared HIR element type (`Str`) was
recovered correctly and then immediately overwritten by the base's **erased**
`Array(i64, 0)` MIR type, which is what a container born from `var a: [text] =
[]` carries. This is the identical erased-`Array(i64)` shape, and the identical
repair, as round 1's `lower_index_expr` fix: let the declared HIR type win, and
map `Str` through `bootstrap_text_type()` (the `Opaque("str")` form) rather than
`lower_type`'s fat-pointer tuple. No-op for a genuine `[i64]`.

### B. `.first()` / `.last()` — FIXED (`expr_dispatch.spl`, `NullCoalesce`)

Not in the `.first()` lowering at all — that one is correct. The loss was in the
`??` arm that consumes its Option: `result_type` there was derived ONLY from the
`??` expression's own HIR annotation, which is routinely nil on the flat
native-build path, so it silently defaulted to i64. The Option's declared INNER
type was already being looked up two lines above (for the struct case) and was
simply not used for anything else. Extending that existing lookup to `Str`,
`Bool` and `Float` fixed six gate cases at once. The bit-level signature that
identified it: `[f64]` printed **4609434218613702656**, the IEEE-754 pattern of
1.5 rendered by `rt_raw_i64_to_string`.

**`.first()` is probed through `?? <default>`, never as bare `{a.first()}`, and
that is deliberate.** The two lanes disagree on what `.first()` RETURNS: the
interpreter yields the bare element, native yields an Option handle. A bare
interpolation therefore compares two different things and says nothing about
element typing. (The interpreter renders a hand-built `Some(77)` as
`<enum@0x...>`, so it has no consistent bare-Option rendering to compare
against either.) That divergence is real but is a separate question from this
bug.

## Still open (measured, root cause located, NOT fixed)

### Nested `[[text]]` / `[[bool]]` — blocked upstream of MIR

Traced with an instrumented `lower_index_expr`. For `n: [[text]]` reading
`n[0][0]`:

```
[idx] read base_local=1  from_base=true erased=true hir_present=true
[idx] after-fallback base=1  is_str=false elem_hir_set=true
[idx] remembered elem hir on local 15
[idx] read base_local=15 from_base=true erased=true hir_present=true
[idx] after-fallback base=15 is_str=false elem_hir_set=false
```

The outer read DOES find `n`'s HIR type and DOES match its `Array(_)` arm. But
the element type it recovers is **not** `Array(Str)`: on the inner read that
type fails to match `Array`/`Slice` at all (`elem_hir_set=false`), while its
enum discriminant is pointer-shaped, i.e. a payload-carrying variant — so it is
something like `Named`/`Generic`, not the nested array kind. The declared
`[[text]]` never arrives in MIR as `Array(Array(Str))`.

A candidate MIR-side fix (calling `remember_local_hir_type` on
`lower_index_expr`'s result local, which it has never done) was written,
measured to change nothing because of the above, and **reverted** rather than
landed as inert code. The real fix belongs in whatever records the declared
container type for a nested array literal, upstream of 50.mir. `[[i64]]` and
`[[f64]]` pass, so the nesting machinery itself works.

### `if val v = <a text Option>:` — separate, general, NOT array-specific

`if val v = a.first():` on a `[text]` prints a raw handle, while the sibling
`a.first() ?? d` is now correct. It reproduces with a plain `fn pick() -> text?`
too, so it is not an array defect and is out of this bug's scope. Root cause
located: `lower_if_chain` (`mir_lowering_stmts.spl:~2380`) recovers the payload
type only for `Float`, via `find_local_hir_type(candidate.id)` on the if-val
BINDING local. Traced: that binding's MIR type is I64 (the gate passes) but
`hir_present=false` — the binding never inherits the initializer's remembered
HIR type, so no payload arm of any kind can fire. Adding `Str`/`Optional(Str)`
arms there was tried and is **unreachable dead code** until the binding inherits
the metadata; it was reverted rather than landed. The `??` path works because it
uses `option_inner_hir_type_for_local`, which falls back to the receiver
EXPRESSION's declared type.

## Stage-1 diagnostic evidence (2026-08-24) — diagnostics ARE readable now

The point of this bug was never formatting: `CompileContext.error_message_at`
returns `self.errors[index]` from a `[text]`, and the diagnostic reporter
iterates that list with `for`. A Stage-2-compiled compiler was SEGVing WHILE
reporting an error it had correctly detected, printing nothing usable.

A full bootstrap was run on the post-fix tree. **Stage 1 built clean** —
`Build complete: 449 compiled, 290 cached, 0 failed` / `Stage 1: OK (27387280
bytes, hash=5ce49cd6...)`. Stage 1 is compiled from the Simple sources, so it
carries both rounds of this fix. Fed a two-line fixture with a deliberate error
(`val x: = 1`), it prints, verbatim:

```
[parser_error] line 2:12: expected type annotation
[parser_error_ctx] path /tmp/lai/s1/bad.spl kind 100 text '='
  line 2:12: expected type annotation
```

That is a **readable diagnostic**, naming the right line, column and message —
the exact `expected type annotation` string the round-1 fixture proxy turned
from `E=RTS\001` into real text. The compiler can now say what is wrong with
your program.

**Two honest limits on this evidence, stated rather than glossed:**

1. **The SEGV is NOT gone.** The run still exits 139 after printing. It is now a
   crash that reports first instead of a silent one, which is what unblocks the
   investigation, but it is still a crash. And it is a SEPARATE defect: the same
   Stage 1 binary also SEGVs on a *valid* hello-world, with
   `[ERROR] MIR error: E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED: retained module
   surface payload malformed at HIR entry (heap-typed payload word is 0 or in
   the zero page)` — nothing to do with text elements. That is the next thread
   to pull, and it is not this bug.
2. **Attribution between round 1 and round 2 is not separated.** `errors[index]`
   is the round-1 `a[i]` fix; `for e in errors` is round 2's. Only a second
   ~35-minute bootstrap of the pre-round-2 tree would split them, and it was not
   run. The claim here is "diagnostics are readable on the post-fix tree", not
   "round 2 alone made them readable".

Stage 3 (the actual self-hosted stage) was not reached: Stage 1 alone took ~35
minutes and the run hit its time cap during the Stage 2 determinism re-check.

## Verified non-regressing

wide `i64` (2^60), negative `i64`, `f64` 0.1, `Dict<text, text>`, plain `text`
and `.len()`, `bool`, class-field `[text]`.
