# Array `.at(i)` on the native LLVM lane — dispatch + missing C runtime accessor

**Date:** 2026-08-01
Status: REOPENED 2026-08-17 — diverges under a PINNED JIT arm (see "Measured arms" below)
Status: ~~CLOSED (not reproducible)~~
~~Status re-verified 2026-08-17 by source inspection (triage shard 00).~~ — that
stamp was source inspection only and is superseded by execution.

## Measured arms 2026-08-17 (engine PINNED, both arms executed)

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
59536728 bytes, mtime 2026-08-16 22:59:37.799277177 +0000 (stale Rust seed).
No rebuild, no redeploy. `rc` read from a variable on the line AFTER the
command, never through a pipe.

Probe (`.at()` inside a `fn`, carrying the in-`fn` 2^60 JIT-compilation control;
a top-level body runs interpreted regardless of the pin, so the control must sit
inside a `fn`):

```
fn pick(a: [i64], i: i64) -> i64:
    return a.at(i)
fn main():
    print("v=" + pick([10, 20, 30], 1).to_string())
    val p60 = 1152921504606846976
    print("pow=" + p60.to_string())
```

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run q06_arrayat.spl   # rc=0
v=20
pow=1152921504606846976

$ SIMPLE_EXECUTION_MODE=jit bin/simple run q06_arrayat.spl           # rc=0
v=6126812864993
pow=-1152921504606846976
```

Expected `v=20`.

**JIT-compilation witness (the sound one).** The negated `pow` above is NOT a
valid witness in general: it depends on the int61 truncation defect still
existing, so on a binary where that is fixed the arms AGREE and the witness
reads backwards. An engine witness must not itself be a defect. Re-verified on
the same binary with the version-independent trace:

```
$ SIMPLE_JIT_TRACE_ADDR=1 SIMPLE_EXECUTION_MODE=jit bin/simple run q06_arrayat.spl
# rc=0, 2 `[jit-addr] <fn> 0x...` lines, 0 jit-fallback lines
```

Two functions were genuinely JIT-compiled and nothing was demoted to the
interpreter, so the divergence above is a real JIT result. Both
arms rc=0, so this is a wrong value, not a crash — NOT an rc=143/137/144
UNVERIFIED. `6126812864993` is an unrelated-looking integer read out of a
still-tagged slot, the same shape as `native_to_i64_nil_coalesce_print_tagbox_leak`'s
`3775049836129`. NOT ASSERTED: a shared root cause with those rows. Another lane
has since refuted the single-untag-root hypothesis (the `<value:0x...>` symptom
is the inverse direction from the `480 == 60 << 3` symptom), so this row is
recorded on its own measurement only.
Expected `v=20`. The negated `pow` proves the JIT arm actually compiled. Both
arms rc=0, so this is a wrong value, not a crash — NOT an rc=143/137/144
UNVERIFIED. `6126812864993` is an unrelated-looking integer read out of a
still-tagged slot, the same shape as `native_to_i64_nil_coalesce_print_tagbox_leak`'s
`3775049836129`. NOT ASSERTED: a shared root cause with those rows. Another lane
has since refuted the single-untag-root hypothesis (the `<value:0x...>` symptom
is the inverse direction from the `480 == 60 << 3` symptom), so this row is
recorded on its own measurement only.
**Parent bug:** `array_at_returns_nil_for_every_index_2026-08-01.md`
**Prior lanes:** interpreter `f18c5963132`, JIT `ceee960ca8e`
**Severity:** CRITICAL — silent wrong answer, no error, no crash

Every measurement below was taken by BUILDING AND RUNNING a real natively
compiled ELF. Nothing here is from review. Each claim is tagged PROVED or
INFERRED and names the lane it covers.

---

## What was actually wrong on native (PROVED)

The parent bug listed three LLVM codegen sites that map the method name `at`
straight to the string-only `rt_string_char_at` with no receiver test:

```
src/compiler_rust/compiler/src/codegen/llvm/emitter.rs:178
src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2371
src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:2097
```

That census is CONFIRMED and it is the COMPLETE family: exactly five sites in
the tree map `at`, and the other two (`codegen/instr/calls.rs:3240`,
`codegen/instr/closures_structs.rs:1366`) were already routed to `rt_at` by the
Cranelift/JIT fix. After this change all five agree.

But the dispatch table was only **half** the native defect. The other half was
invisible from the Rust tree entirely:

**`rt_at` and `rt_array_at` did not exist in the C native runtime.** They were
added in `ceee960ca8e` to the *Rust* runtime
(`src/compiler_rust/runtime/src/value/collections.rs`) only. The native lane
links `src/runtime/runtime_native.c`, which had `rt_array_get` / `rt_array_len`
and no `at` accessor of any kind.

This is exactly the "fixing only the first leaves the lane wrong" shape the
parent bug warned about, and it surfaced as a **loud link failure**, not a
silent one — `error: codegen: undefined symbol: rt_at` — because
`linker/native_binary/stubs.rs::check_no_fake_rt_stubs` hard-fails any `rt_*`
symbol the real runtime does not define instead of fabricating a zero-returning
stub. That gate did its job here and is worth keeping.

---

## Measurement — native LLVM lane, unpatched vs patched (PROVED)

Probe: `at_nomatch.spl`, compiled with
`simple compile <src>.spl --native --backend llvm -o <out>` and then RUN.
Both runs use the identical invocation, cwd, and runtime-archive resolution;
the only difference is the compiler binary.

Positive artifact asserted, not the absence of an error: a 4,480,400-byte ELF
64-bit LSB pie executable that runs and prints.

| assertion | correct | unpatched | patched |
|---|---|---|---|
| `xs.at(0)` on `[10,20,30,40,50]` is PRESENT | PRESENT | **ABSENT — FAIL** | **PRESENT — PASS** |
| `xs.at(99)` is ABSENT | ABSENT | ABSENT — pass **VACUOUSLY** | PRESENT — FAIL (see below) |

**The non-vacuity evidence is the first row.** It is the only assertion that can
tell "absent" apart from "unimplemented", and it is the one that flips. The
second row passed unpatched for the wrong reason: unpatched `.at()` reported
absence for *every* index, so an out-of-range check could not fail.

This is the first time the native lane has been measured at all. The parent bug
recorded the native row as "silent nil for every index — NOT verified"; that
prediction is now CONFIRMED by transcript.

### Why row 2 is not a regression introduced here (PROVED)

Row 2 reads PRESENT after the fix because `b == nil` is an **expression-form**
nil comparison, which lowers to a raw `subject == nil` compare. A boxed
`Option::None` is a heap object and is never raw-equal to the nil sentinel.

The already-landed, already-accepted **JIT** lane produces the **identical**
output for the same source on the same binary:

```
JIT lane (bare `simple at_nomatch.spl`):  at(0) PRESENT / at(99) PRESENT
native LLVM lane (after this fix):        at(0) PRESENT / at(99) PRESENT
```

So this is a **pre-existing cross-lane gap, not a native regression**, and this
change brings native to **exact parity with the fixed JIT lane** — which is the
stated acceptance goal. Filed separately below.

---

## Encoding decision — re-verified on the native lowering, not assumed

The parent bug settled on the boxed `Option`. That conclusion was re-derived
against the C runtime rather than carried over, because the two backends have
diverged before. It holds, for the *same* reason and one extra:

- `rt_array_get` returns **raw i64 element words** and reports a miss by
  returning the raw nil sentinel `3` (`RT_NIL = (SPECIAL_NIL << 3) |
  TAG_SPECIAL`). A flat/raw optional built on it therefore cannot distinguish
  an element whose value **is** 3 from absence, by construction. `xs.at(3)` on
  `[0,1,2,3,4]` is precisely that case.
- `rt_array_get` also **normalizes negative indices Python-style**
  (`if (idx < 0) idx = len + idx`), so building `at` on it would make `at(-1)`
  silently wrap to the last element instead of reporting absence.

`rt_array_at` therefore does neither. Bounds are checked SIGNED and
UNNORMALIZED — present iff `0 <= index < len`, matching the interpreter arm from
`f18c5963132` and the Rust runtime's `rt_array_at` — and the result is a
**canonical boxed Option**: `rt_enum_new(1, 0, elem)` for `Some`,
`rt_enum_new(1, 1, nil)` for `None`. Enum id 1 with ordinal Some=0/None=1 is the
representation `rt_is_none()` in the same file already recognizes.

The `Some` payload is the **raw element word**, matching what `xs[i]`
(`rt_array_get`) yields on this lane, so `.at()` and `[i]` cannot silently
disagree.

`rt_at` does the receiver test at runtime (`rt_core_as_array`), the same shape
as the Cranelift `rt_at`, because the codegen sites dispatch purely on method
name and do not all have a reliable static receiver type. **Text `.at()` is
unchanged** — still a raw single-character string, not an Option.

---

## Blocking defects found on the native lanes while verifying (PROVED)

These are independent of `.at()`, were reproduced with minimal programs
containing no `.at()` at all, and are the reason this lane cannot be verified
through a `match` today. Both are filed separately.

**1. `native-build --backend llvm`: every user-defined function call returns 0.**

```simple
fn add(a: i64, b: i64) -> i64: return a + b
fn ret_const() -> i64: return 42
# in main: inline `2 + 3` == 5 is CORRECT;
#          ret_const() returns 0;  add(2,3) returns exactly 0
```

Build exits 0, emits a real ELF, prints no error, and does **not** print the
"dropped to the interpreter" fallback notice. The JIT lane runs the same source
correctly. `--backend cranelift` fails to build at all.

**2. `compile --native`: any function containing a `match` is refused.**

```
error: semantic: cannot compile to standalone native binary:
  N function(s) contain constructs that require the interpreter:
  - <fn>: [PatternMatch]
```

Reproduced with a `match` over a plain user `fn -> i64?` and no `.at()`. This is
why the probe above uses the `== nil` expression form rather than the canonical
`match`/`Some`/`None` shape, and why an 11-example port of
`test/01_unit/lib/common/array_at_option_spec.spl` cannot run on this lane yet.

**3. `native-build` runs the PURE-SIMPLE compiler, not the Rust seed** — and its
MIR lowering has no `at` arm at all, so it fails LOUDLY with
`MIR lowering error: unresolved method call: at` from
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`. That is a
different lane from the Rust LLVM backend fixed here and is still OPEN. (The 32
`unresolved method call: merge` errors in the same log are pre-existing stdlib
noise and are not fatal; the `at` one is what aborts the build.)

---

## Sibling gap, filed not fixed: `== nil` cannot see a boxed `Option::None`

`ceee960ca8e` fixed the **pattern** form — `Pattern::Literal(Expr::Nil)` now
lowers to `rt_is_none`, so `case nil:` and `case None:` agree on every
representation. The **expression** form `x == nil` was not part of that sweep
and still lowers to a raw pointer compare, so it reads a boxed `Option::None` as
non-nil on **both** the JIT and native LLVM lanes (transcript above).

This is a textbook "a sweep that doesn't enumerate the family leaves siblings"
case: same defect, same cause, adjacent spelling. It is NOT fixed here because
routing every `==`-against-nil through `rt_is_none` is a general change to
equality semantics for all code, well outside an `.at()` fix, and it needs its
own verification pass. Recorded so it is not rediscovered as a mystery.

---

## Verification bar for anyone extending this

- **`simple test` cannot verify any of this.** The test-runner apps are pinned
  to the interpreter by `run_file_with_interpreter_mode`, so a green suite says
  nothing about native codegen. Run assertions as a plain compiled program.
- **A bare `simple foo.spl` is the JIT**, not native.
- **`native-build` is the pure-Simple compiler**; `compile --native` is the Rust
  seed's LLVM backend. They are different lanes with different defects.
- **Assert a positive artifact** — a real ELF that runs and prints the expected
  value. The default JIT exits 0 while printing "whole module dropped to the
  interpreter"; a clean exit proves nothing.
- **Runtime-archive resolution is cwd/exe sensitive.** Running the compiler from
  a directory whose ancestors contain no built `libsimple_native_all.a` produces
  `undefined symbol: rt_at` even when the symbol exists in the archive you just
  built. Confirm with `nm --defined-only <archive> | grep -w rt_at` and run the
  compiler from a directory where resolution finds that archive.
