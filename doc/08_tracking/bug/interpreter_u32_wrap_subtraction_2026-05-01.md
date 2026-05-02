# Interpreter `0u32 - (x >> 31u32)` does not wrap to `0xFFFFFFFF`

**Status:** Open (worked around in F's LZMA2 lane)
**Date filed:** 2026-05-01
**Discovered by:** F's range-coder work in `src/lib/common/compress/lzma2.spl`
  (commit `ede1266ef3` — `feat(lzma2): pure-Simple range coder + LZMA2
  compressed chunk decode`; jj change `oxtxxvlsylxo`).

## Symptom

The classic LZMA range-coder mask trick

```simple
val mask: u32 = 0u32 - (code >> 31u32)
```

is supposed to produce `0xFFFFFFFF` when the high bit of `code` is set and
`0u32` otherwise. In Simple's interpreter, the subtraction does not wrap as
unsigned 32-bit; instead the value comes out as the signed integer `-1`
(internally `Value::Int(-1i64)`), so any subsequent unsigned arithmetic that
treats the result as a 32-bit mask is silently wrong.

## Minimal repro

`/tmp/u32_wrap_repro/main.spl` (do **not** commit):

```simple
fn main():
    val a: u32 = 0u32 - (1u32 >> 0u32)
    val b: u32 = 0u32 - 1u32
    val c: u32 = 1u32 >> 0u32
    val d: u32 = (123u32 >> 31u32)
    val e: u32 = 0u32 - (123u32 >> 31u32)
    val f: u32 = 0u32 - ((1u32 << 31u32) >> 31u32)
    print "a={a}"
    print "b={b}"
    print "c={c}"
    print "d={d}"
    print "e={e}"
    print "f={f}"
```

Run via the release binary (the bare `bin/simple <file.spl>` wrapper currently
falls through to the REPL — pass `run` to the underlying binary; tracked
separately, see memory note `feedback_simple_run_wrapper_broken.md`):

```bash
bin/release/x86_64-unknown-linux-gnu/simple run /tmp/u32_wrap_repro/main.spl
```

### Observed output (2026-05-01)

```
a=-1
b=-1
c=1
d=0
e=0
f=-1
```

### Expected output (treating values as u32)

```
a=4294967295   # 0xFFFFFFFF
b=4294967295   # 0xFFFFFFFF
c=1
d=0
e=0
f=4294967295   # 0xFFFFFFFF
```

`a`, `b`, and `f` should each be `0xFFFFFFFF` (i.e. `4294967295`); the
interpreter instead yields the signed value `-1`. `c`, `d`, `e` are correct
(no wrap needed). This confirms F's diagnosis: the masked-bit idiom does not
wrap. The "expected behavior also occurs" branch of AC-2 therefore does
**not** apply — F's workaround stays in place.

## Suspected interpreter site / root cause

`src/compiler_rust/compiler/src/interpreter/expr/ops.rs` around line 529, the
`BinOp::Sub` arm:

```rust
BinOp::Sub => {
    if use_float { ... }
    else if let Some(result) = try_dunder_binop("__sub__", ...) { result }
    else {
        Ok(Value::Int(left_val.as_int()? - right_val.as_int()?))
    }
}
```

The interpreter has no distinct `u32` runtime representation — every integer
is held as `Value::Int(i64)`. `BinOp::Sub` calls `as_int()` on both operands
and returns a signed i64 result; there is no modulo-2^32 mask applied even
when the source-level types are both `u32`. So `0u32 - 1u32` lowers to
`0i64 - 1i64 = -1i64`, not `0xFFFFFFFFu32`.

The narrow title scopes this to subtraction (because that's where F hit it),
but the same root flaw should affect any binary op that ought to wrap as
u32: `Add` overflow, `Mul` overflow, `Neg`, etc. Those code paths follow the
same `Value::Int(... as_int() OP as_int() ...)` shape in `ops.rs`. They are
*not* exercised by F's workaround and are *not* verified by this repro;
recording the suspicion so a fixer can decide whether to widen the scope or
file follow-up bugs.

## Workaround

F replaced the mask idiom with an explicit compare + branch in
`_lzma_decode_direct` (`src/lib/common/compress/lzma2.spl:228-248`):

```simple
# Branch on (code >= range) instead of computing a wrap-around mask --
# avoids relying on u32 wrap semantics that vary across the
# interpreter and compiled backends.
if cur.code_v >= cur.range_v:
    cur.code_v = cur.code_v - cur.range_v
    result = (result << 1) + 1
else:
    result = result << 1
```

This is portable across backends and matches the LZMA reference's effective
semantics. Any pure-Simple code currently using `0u32 - bit_value` to
synthesise a mask should switch to the same branchful form until the
interpreter gains real u32 wrap semantics.

## Impact

Any pure-Simple code using the `0u32 - bit` mask idiom — or otherwise
relying on u32 (or by extension u8/u16/u64) wrap-around semantics for
unsigned subtraction in interpreter mode — is silently broken. Concretely
at risk:

- LZMA / LZMA2 range-coder mask tricks (already worked-around in F's lane)
- Other range / arithmetic coders
- CRC32 polynomial-reduction code that builds masks from a sign bit
- Bignum/UInt utility code that relies on borrow-from-zero semantics
- Constant-time crypto primitives that build masks from comparisons

Compiled-mode (Cranelift / LLVM backend) behavior was **not** verified in
this report; F's source comment ("wrap semantics that vary across the
interpreter and compiled backends") suggests compiled mode may also be
affected, but that needs its own repro before it can be claimed.

## Cross-references

- Workaround commit (jj `oxtxxvlsylxo`, git `ede1266ef3`):
  `feat(lzma2): pure-Simple range coder + LZMA2 compressed chunk decode`
- Workaround call site:
  `src/lib/common/compress/lzma2.spl` `_lzma_decode_direct`
  (lines ~228-248, comment at lines 239-241)
- Suspected interpreter site:
  `src/compiler_rust/compiler/src/interpreter/expr/ops.rs:529`
  (`BinOp::Sub` arm, `Value::Int(... - ...)`)
- Related memory note: `feedback_simple_run_wrapper_broken.md`
  (re: `bin/simple <file.spl>` wrapper falling through to REPL — orthogonal
  but encountered while reproducing)

## Suggested fix direction (not prescriptive)

The interpreter would need to either (a) carry the source-level integer type
on `Value` so it can mask after each arithmetic op, or (b) when both
operands originate from a `u32`-typed expression, mask the i64 result to
`0xFFFFFFFF`. Option (b) is cheaper but requires type information to flow
into `evaluate_binop`. Per `feedback_bug_doc_fixes_are_guesses.md`, this is
a hypothesis only — verify against the actual interpreter Value/type model
before implementing.
