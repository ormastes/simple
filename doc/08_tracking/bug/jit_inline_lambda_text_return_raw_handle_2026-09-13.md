# Bug: JIT-compiled inline lambda returning `text` yields a raw handle integer

Status: OPEN — reproduced 2026-09-13. Silent wrong answer (no error, no
diagnostic); the interpreter path is correct, so this is a JIT-only divergence.

**Date:** 2026-09-13
**Area:** compiler / Cranelift JIT / closure ABI
**Severity:** high — silently wrong values, no diagnostic

## Host and binary identity (measured)

- Windows 11 x86_64, Git Bash.
- `bin/simple` -> Rust bootstrap seed, `Simple Language v1.0.0-rc.1`.
- `src/compiler_rust/target/release/simple.exe`, 39,265,792 bytes, Sep 13 08:23.

## Symptom (measured)

Any lambda whose **return type is `text`**, when passed inline to a
higher-order builtin such as `Array.map`, is JIT-compiled and returns a
pointer-like integer instead of the string. `i64` returns are unaffected.

`scratch_lam2.spl`:

```simple
fn main():
    val a = ["ab", "cd"].map(\z: z)
    print(a[0])
    val b = ["ab", "cd"].map(\z: z + "!")
    print(b[0])
    val c = ["ab", "cd"].map(\z: z.len())
    print(c[0])
    val d = ["ab", "cd"].map(\z: z.upper())
    print(d[0])
    val e = [1, 2].map(\v: "n{v}")
    print(e[0])
```

`bin/simple run scratch_lam2.spl` prints:

```text
4003547163073      <- expected "ab"
4003547452513      <- expected "ab!"
2                  <- correct (i64 return)
4003547169729      <- expected "AB"
4003547170017      <- expected "n1"
```

Consecutive values differ by small multiples of 32, consistent with a heap
address / tagged handle for the `text` value rather than its contents.

## Control proving the interpreter is correct (measured)

A lambda **bound to a variable** trips an existing JIT closure-ABI guard, which
demotes the whole function to the interpreter. Adding one such lambda as a
control makes every case above correct.

`scratch_lam4.spl`:

```simple
fn main():
    # Control: this bare lambda trips the JIT closure-ABI guard for the whole
    # function, so everything below runs in the interpreter.
    val guard = \q: q
    print(guard("x"))
    val a = ["ab", "cd"].map(\z: z)
    print(a[0])
    val b = ["ab", "cd"].map(\z: z + "!")
    print(b[0])
    val d = ["ab", "cd"].map(\z: z.upper())
    print(d[0])
    val e = [1, 2].map(\v: "n{v}")
    print(e[0])
    val p = ["ready"].map("{_1}:migrated")
    print(p[0])
```

`bin/simple run scratch_lam4.spl` prints the guard message and then correct
values throughout:

```text
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: function 'main' creates a lambda/closure the JIT closure ABI cannot compile (the call boundary types [TypeId(14)] -> TypeId(14) are not carryable across the closure ABI (ANY means no encoding is correct for both an integer and a float)); JIT would return wrong values or crash; deferring to interpreter
x
ab
ab!
AB
n1
ready:migrated
```

The guard's own text — "JIT would return wrong values or crash" — describes
exactly the failure that occurs when it does **not** fire.

## Scope established by measurement

Correct under JIT:

- `[1, 2].map(\v: v + 1)` -> `2`
- `["ab", "cd"].map(\z: z.len())` -> `2`
- `["ab", "cd"].filter(\z: z == "ab")` -> `.len()` is `1`
- `["ab"].map(named_fn)` where `named_fn(z: text) -> text` -> `ab`

Wrong under JIT: every lambda whose result is `text`.

So the **argument** side of the closure boundary is fine (comparison and method
dispatch on `z` both behave), and a **named** function with declared types is
fine. Only the inline-lambda `text` **return** is mis-decoded.

## Second symptom: the JIT also accepts what the interpreter rejects (measured)

`["ab", "cd"].map("K")` — a plain string with no placeholder, which is *not* a
valid callback (the supported constant form is `\_: "K"`, per
`short_grammar_constant_callback_form_missing_2026-05-27.md`).

- Interpreter (forced via the bare-lambda control): correctly refuses with
  `error: semantic: expected lambda or function argument`.
- JIT: no error; `a[0]` is the empty string.

So the divergence is bidirectional — the JIT silently produces a wrong value
where the interpreter produces a correct diagnostic. Same root cause area.

## Root cause (read from source 2026-09-13 — static, not yet proven by a fix)

Two independent defects compound; either alone would let the bad value through.

**1. The guard is never reached for the inline form.**
`src/compiler_rust/compiler/src/codegen/jit.rs:336-359` only inspects
`MirInst::IndirectCall` instructions *inside the enclosing function*. That is
the shape a `val f = \x: ...` binding lowers to, which is why the bare-lambda
control in `scratch_lam4.spl` trips it. For `["ab"].map(\z: z)` the lambda is
invoked by the RUNTIME (`rt_array_map` dispatching through
`rt_closure_func_ptr`), so `main`'s MIR contains no `IndirectCall` at all and
the boundary is never examined.

**2. Even if reached, the predicate would admit it.**
`jit_closure_abi_supports` (`src/compiler_rust/compiler/src/codegen/mod.rs:91-100`)
rejects only `ANY`, `VOID` and `BOOL`, then admits anything that lowers to
Cranelift `I64` or `F64`. `text` lowers to `I64` (it is a pointer), so a
`text -> text` boundary is classified carryable. The boxed-closure entry
(`codegen/closure_boxed_entry.rs`) uses the all-`RuntimeValue` convention, so
the raw pointer is transported where a tagged `RuntimeValue` is expected — which
is precisely the pointer-shaped integer observed.

`i64` is unaffected because a raw `i64` and its transported form coincide;
`z.len()` returns `i64`, which is why that one case is correct.

## Suggested fix (not applied here)

Two edits, both conservative:

- widen `jit_closure_abi_supports` to reject heap/reference-shaped types
  (`text` and friends) rather than admitting every `I64`-lowering type; and
- extend the jit.rs scan so a lambda passed directly as a call argument has its
  own signature checked, not just `IndirectCall` boundaries in the enclosing
  function.

Not attempted in this session: it requires rebuilding the Rust bootstrap seed,
which on this Windows host needs the MSVC environment and carries the known
stale-`simple.exe` hazard, and the second edit is a MIR-walker change rather
than a one-line predicate tweak. Filed rather than half-fixed.

## Impact on existing entries

Three 2026-05-27 short-grammar entries were closed "STALE — verified working":

- `short_grammar_placeholder_interpolation_2026-05-27.md`
- `short_grammar_placeholder_value_binding_interpreter_2026-05-27.md`
- `short_grammar_atom_swap_interpreter_2026-05-27.md`

Those closures remain **correct for the interpreter** — `scratch_lam4.spl`
re-proves `["ready"].map("{_1}:migrated")` -> `ready:migrated` in interpreter
mode on 2026-09-13. They are not reopened. What they did not cover is the JIT
path, which is what this entry tracks.

## Suggested fix direction

Conservative: make the JIT defer (widen the guard) rather than teach the closure
ABI to encode `text` returns. Deferring restores correct behaviour immediately
and costs only JIT coverage; encoding `text` across the closure ABI is a
feature, not a bug fix.
