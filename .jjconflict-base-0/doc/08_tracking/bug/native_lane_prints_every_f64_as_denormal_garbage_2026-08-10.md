# The native lane prints EVERY f64 as denormal garbage, not just computed ones

- **Date:** 2026-08-10
- **Status:** RESOLVED 2026-08-11 — see "Root cause" and "Fix" below.
- **Resolved-by-layer:** C runtime (`src/runtime/`), NOT the Simple layer and
  NOT the compiler. Both backends and the Rust runtime were already correct;
  the C runtime was the sole outlier, so the fix-in-`.spl`-not-Rust rule does
  not apply (there is no `.spl` implementation of this ABI).
- **Gate:** `scripts/check/check-native-f64-stdout-oracle.shs`
  (PASS — 8 fixtures, stdout compared against the interpreter, live negative
  control, both halves individually revert-proven).
- **Lane:** native only (`native-build`). Interpreter and JIT are correct.
- **Class:** silent wrong-value, total for the type.

## Symptom

```
fn main():
    val b: f64 = 16.0
    val c: f64 = b.sqrt()
    print c
    print b
```

```
SIMPLE_NATIVE_BUILD_RUST=1 simple native-build --source natsrc \
    --entry natsrc/nat2.spl -o n2 && ./n2
0.0000000000000000000000000000000000000000000000000000000000...
0.0000000000000000000000000000000000000000000000000000000000...
```

Both lines are denormal garbage — **including `print b`**, which is a plain
typed float local holding a literal `16.0`. No method call, no computation, no
argument-position subtlety. The native lane cannot render any `f64`.

The magnitude (~1e-313) is what an `i64` looks like when its bit pattern is
reinterpreted as a double, so the value is reaching the formatter as an integer
word and being bit-cast rather than converted — the mirror image of the
interpreter/JIT defect in
`float_returning_method_in_argument_position_prints_tagged_bits_2026-08-10.md`,
where a float word was read as an integer.

## Why this is filed separately, and how it was isolated

Found while verifying the argument-position fix across lanes. The tempting
reading was that the fix regressed native: before the fix native printed
`577023702256844800` (the tagged bits) for `print b.sqrt()`, and after it
printed this garbage instead. The control above rules that out — `print b` on a
**literal-initialised** float is equally broken, identically, on a binary built
from unmodified `bb43fac0cf5` and on the fixed one. The lane was already unable
to print floats; the fix only changed which wrong thing it prints, by making the
value take the (broken) float rendering path instead of the integer one.

Note the default pure-Simple `native-build` refuses to run from a bare seed
("pure-Simple tool 'native-build' unavailable; refusing Rust fallback"), so this
was measured through the Rust `native_project` pipeline via
`SIMPLE_NATIVE_BUILD_RUST=1`. Whether the pure-Simple native path shares the
defect is UNMEASURED.

## Root cause — TWO stacked defects, both in the C runtime

Codegen was exonerated first by disassembly. For `val b: f64 = 16.0; print b`
the emitted `spl_main` is exactly right:

```
movabs $0x4030000000000000,%r8     # 16.0
vmovq  %r8,%xmm0                   # ... in xmm0
call   *%r9                        # -> rt_value_float
mov    %rax,%rdi
call   *%r9                        # -> rt_println_value
```

So the value is correct in memory and correct at the call boundary. This is a
**rendering defect, not a boxing-decision defect** — but it takes two fixes,
because two independent bugs sit on the rendering path:

**1. ABI mismatch in `rt_value_float`** (`src/runtime/runtime_native.c:2237`
pre-fix). Every backend calls it with an `f64` —
`RuntimeFuncSpec::new("rt_value_float", &[F64], &[I64])`
(`src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:548`), and the LLVM
backend builds `call @rt_value_float(double ...)`
(`codegen/llvm/functions.rs:379-383`). The Rust runtime agrees:
`pub extern "C" fn rt_value_float(f: f64)`
(`src/compiler_rust/runtime/src/value/sffi/value_ops.rs:11`) — which is why the
JIT lane was fine. The C runtime alone declared `int64_t rt_value_float(int64_t
raw_bits)`, so under SysV x86-64 it read **`%rdi`** while the caller passed
**`%xmm0`**. Confirmed in the linked binary: `rt_value_float` opens with
`mov %rdi,%rbx`. Every f64 boxed in the native lane therefore picked up an
unrelated integer register.

**2. Heap-box decode missing in `rt_to_string`** (`runtime_native.c:2794-2803`
pre-fix). The float branch decoded only the **legacy inline `TAG_FLOAT`** form:

```c
uint64_t bits = ((uint64_t)value) & ~RT_VALUE_TAG_MASK;
```

But `rt_value_float` returns the **lossless heap box** — a `TAG_HEAP` pointer to
an `RtCoreFloat`. For that value the expression above is the **malloc pointer**,
bit-cast to a double. That is the denormal: after fixing (1) alone the output
was still garbage but now *drifted upward across successive calls*
(`...2172943556`, `...2172975966`, `...2172977864`) — the signature of a heap
pointer, which is what identified this second defect. `rt_core_as_heap_float()`
already existed and was simply never called from this path.

Fixing either half alone still prints garbage; both are revert-proven below.

## Fix

- `src/runtime/runtime_native.c` — `rt_value_float` takes a `double`; bit
  pattern recovered by `memcpy` internally. Internal caller (`rt_string_to_float`
  tail) passes the parsed `double` directly.
- `src/runtime/runtime_native.c` — `rt_to_string` tries `rt_core_as_heap_float()`
  **before** the legacy inline decode, mirroring the existing heap-wide-int
  branch in `rt_core_print_value_to`.
- `src/runtime/runtime.h` — declaration updated to `double`.
- `src/runtime/test/rt_dict_float_key_exactness_selfcheck.c`,
  `rt_transient_heap_scope_selfcheck.c` — these passed only because both sides
  shared the *wrong* ABI; updated to pass a `double`. The dict selfcheck's
  comment claiming it "exercises the SAME representation compiled Simple code
  produces" was false before this change and is true now.

## Verification (oracle = stdout vs interpreter, never build success)

`scripts/check/check-native-f64-stdout-oracle.shs`, 8 fixtures:

| form | native (pre-fix) | native (post-fix) | interpreter |
|---|---|---|---|
| `val n: i64 = 42` (positive control) | `42` | `42` | `42` |
| `val b: f64 = 16.0; print b` | `0.000…449699294` | `16.0` | `16.0` |
| `print 3.5` | `0.000…` | `3.5` | `3.5` |
| `b + 1.5` | `0.000…` | `17.5` | `17.5` |
| `print "V={b}"` | `V=0.000…` | `V=16.0` | `V=16.0` |
| f64 returned from fn | `0.000…` | `2.5` | `2.5` |
| `0.1` (low mantissa bits set) | `0.000…` | `0.1` | `0.1` |
| negative control | reports mismatch | reports mismatch | — |

`PASS — 8 fixture(s) checked`, exit 0. Revert-proofs, each run to a verdict:

- Revert the heap decode only → `FAIL — 6 of 8`, exit 1.
- Revert the ABI only → `FAIL — 5 of 8`, exit 1.

The `0.1` row is the guard against a future regression back to the lossy inline
box, which zeroes the low 3 mantissa bits.

## Adjacent finding: native-build silently links a STALE runtime archive

While verifying, the same fix appeared **inert** when built from the repo root
and **worked** when built from any other cwd. Cause: native-build resolves its
runtime provider through a **cwd-relative** path — `SIMPLE_TRACE_RUNTIME_ROOTS=1`
prints `Runtime retention source: build/simple-core/libsimple_runtime.a`. That
prebuilt archive is never staleness-checked against `src/runtime/*.c`; the local
copy was dated 2026-08-04 against sources from 2026-08-10, so it silently
shadowed the fix. From a neutral cwd the C runtime is compiled from source.

This is a fail-open of its own: **any** C-runtime fix can look like it did
nothing, or a stale bug can look alive, depending only on the caller's cwd. The
gate above builds from a neutral cwd and documents why. TODO: make native-build
either resolve the runtime provider from the repo root rather than the cwd, or
fail when the archive is older than the C sources it was built from.

## Adjacent defects filed in the same round: SEPARATE root cause, not shared

Checked rather than assumed. All three reproduce **in the interpreter**, which
never links this C runtime, so none of them can share a root cause with the
ABI/heap-decode pair fixed here (measured on the deployed seed binary):

| probe | result | reading |
|---|---|---|
| `print b.sqrt()` | `577023702256844800` | `× 8 = 0x4010000000000000 = 4.0` — sqrt IS applied, the *value is right*; only the rendering is wrong. This is the already-filed argument-position tagged-bits defect, fixed in `9c994181c1a` but not present in the deployed seed. |
| `print (16.0).sqrt()` | `16.0` | literal receiver returns the receiver — the method is genuinely never applied. Distinct frontend defect, stays filed in `float_literal_receiver_method_call_returns_receiver_2026-08-10.md`. |
| `n.abs()` / `(2.0).trunc()` / `.pow()` | `Function 'i64.abs' not found`, then `unresolved symbol` | resolution gap, stays filed in `float_and_int_math_methods_missing_on_numeric_receivers_2026-08-10.md`. |

So the "native cannot render f64" defect is fully closed by the runtime fix, and
the other two remain open on their own tickets, unchanged.

## Related

- `doc/08_tracking/bug/float_returning_method_in_argument_position_prints_tagged_bits_2026-08-10.md`
- `doc/08_tracking/bug/f64_integral_to_text_drops_fraction_2026-07-25.md`
