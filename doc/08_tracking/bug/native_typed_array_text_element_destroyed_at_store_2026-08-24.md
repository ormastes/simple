# native lane: a `text` element is DESTROYED at the STORE, not lost at the read

- Status: FIXED (2026-08-24) for `[i64]` / `[text]` / `[bool]` / `[f64]`.
- Gate: `scripts/check/check-native-array-element-type.shs`
  - before: `FAIL — 4 case(s) checked, 3 diverged: text bool f64`
  - after:  `PASS — 4 case(s) checked, 0 diverged`
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

## Still open (measured, not caused by this change)

- `.first()` / `.last()` on a `[text]`: prints the raw tagged handle as an
  integer. Read path never calls `decode_runtime_value`.
- `for x in a` on a `[text]`: same.
- Nested `[[text]]`: `nested[0][0]` prints a raw word. Equally wrong before
  (`N=100461412424641`) and after (`N=97182983609281`) this change.

## Verified non-regressing

wide `i64` (2^60), negative `i64`, `f64` 0.1, `Dict<text, text>`, plain `text`
and `.len()`, `bool`, class-field `[text]`.
