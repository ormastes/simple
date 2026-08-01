# Native link fabricates weak, empty definitions for unimplemented `@extern` fns

- **Date:** 2026-08-01
- **Status:** FIXED (link-side guard landed). Codegen-side fabrication NOT fixed — see "Remaining".
- **Lane:** C1, native link path (Rust seed).
- **Family:** "an unregistered extern silently returns nil/0 on every lane."
  Interpreter lanes were fixed/gated earlier; this is the native-lane member.
- **Component:** `src/compiler_rust/compiler/src/linker/native_binary/`

## Symptom

An `@extern fn` with no implementation anywhere links clean and produces a
runnable binary. There is no link error and no diagnostic. Every call to the
symbol silently returns garbage.

Real-world instance already observed in the family: `src/lib/gc_async_mut/game2d/transform.spl`
declares `@extern fn _cos(x: f64) -> f64` and `@extern fn _sin(x: f64) -> f64`
with no implementation, so every rotated `Transform2D` computed a garbage world
matrix instead of failing.

## Root cause (measured, not assumed)

When an `@extern fn foo(...)` has no implementation, codegen does **not** leave
`foo` undefined. It emits a **weak, zero-size definition** of `foo` into the
object:

```
$ nm -S main.o
0000000000000000 W lane_definitely_absent      <- weak, DEFINED, no size, empty body
0000000000000000 000000000000000a T spl_main
```

Because the symbol is thereby *defined*, it never appears in `nm -u`. The
existing task-#97 guard `check_no_fake_rt_stubs` (`linker/native_binary/stubs.rs`)
reads `nm -u` output, so it is **structurally unable** to see the symbol.

Two consequences follow, and the second one was the surprise:

1. The `starts_with("rt_")` filter in that guard means a missing non-`rt_`
   symbol that *does* reach `nm -u` gets a fabricated weak `return 0` body from
   `gen_stub_code` with no error.
2. More importantly, **the `rt_` half of the guard does not work either** for
   the `@extern`-without-implementation case, for the reason above. Widening or
   narrowing the prefix filter alone therefore fixes nothing.

### Why the `rt_` prefix filter exists (do not simply remove it)

`check_no_fake_rt_stubs` compares undefined symbols against
`real_runtime_defined_symbols()`, which reads only `libsimple_runtime.a` /
`libsimple_compiler.a`. Non-`rt_` undefined symbols are legitimately satisfied
by libc/libm/system libraries that this function cannot see, so a blanket
extension of *that* guard to all undefined symbols would hard-fail on ordinary
libc references. The prefix filter is doing real work; the correct fix is a
different guard at a different observation point, not a wider filter.

## Reproduction (RED)

Seed binary `src/compiler_rust/target/bootstrap/simple`, relative invocation,
artifact asserted, live known-good control in the same run.

```
# p_nonrt.spl
@extern fn lane_definitely_absent(x: i64) -> i64
fn main() -> i64:
    return lane_definitely_absent(41)

# p_rt.spl  -- same, with an rt_-prefixed name
# p_ctrl.spl -- control, no extern: fn main() -> i64: return 7
```

`simple compile <file>.spl --native -o <file>.bin`:

| case | build exit | artifact | run |
|------|-----------|----------|-----|
| `p_nonrt` (non-`rt_` absent extern) | 0 | YES | hangs (timeout 124) |
| `p_rt` (`rt_` absent extern) | 0 | YES | hangs (timeout 124) |
| `p_ctrl` (control, no extern) | 0 | YES | **exit 7, correct** |

Reproduced identically **with and without** `SIMPLE_BOOTSTRAP=1`, confirming the
fabrication is in codegen and not in the bootstrap-gated auto-stub generator.

False-positive check: a real program (structs, `List<i64>`, string
interpolation, `print`) compiled through the same path yields **0** weak
zero-size definitions and runs correctly (`p=4,6`, `sum=15`, exit 0).

## Fix

New guard `check_no_fabricated_extern_definitions` in
`linker/native_binary/stubs.rs`, called from `builder.rs` on **every** link
(not gated on `bootstrap_mode`, because the fabrication is upstream of it).

It reads `nm --defined-only -S <obj>` and rejects any symbol that is weak (`W`)
**and** has no size. A weak zero-size function symbol has no body by
construction, so the test needs no heuristic and cannot false-positive on a real
function: Cranelift's `Preemptible` linkage also produces weak symbols, but a
real function always carries a non-zero size.

The failure is loud and named — it lists every offending symbol and the object
path.

There is **no env hatch and no allowlist** on this path, by design.

### Exemptions

- **Freestanding targets** (`TargetOS::Any | None | SimpleOS`) are skipped.
  Baremetal intrinsics — the `@extern("bare", ...)` family — are legitimately
  absent at compile time and are resolved by the boot layer. Those links go
  through `pipeline/native_project/stubs.rs`, which has its own per-entry
  fabricated-stub ratchet (`config/freestanding_fabricated_stub_baseline.sdn`).
- **MSVC** toolchains report symbols in a different format; skipped rather than
  misparsed.
- If `nm` cannot be run or fails, the guard fails **open** (same policy as the
  #97 guard) rather than blocking targets it cannot inspect.

Note on the `@extern("bare", ...)` marker: it is a *declaration-side* tag and
does not reach this layer. The string `"bare"` appears nowhere in
`src/compiler_rust/compiler/` or `src/compiler_rust/runtime/`; the 38 `bare`
externs live in `src/compiler_rust/lib/std/src/bare/`. The exemption is
therefore expressed as a target-class check, which is the same population.

## Regression test

`src/compiler_rust/compiler/tests/native_binary_rt_guard.rs` ::
`rejects_fabricated_weak_empty_extern_definitions` — three cases: non-`rt_`
fabricated extern must fail and name the symbol; `rt_` fabricated extern must
fail and name the symbol; and a non-vacuity control object with no fabricated
symbols must still link.

## Remaining (not fixed here)

The **codegen** still emits weak zero-size definitions for unimplemented
`@extern` declarations. This guard catches them at the link, which closes the
silent-wrong-answer hole, but the right long-term fix is for codegen to leave
such a symbol *undefined* (an `External` declaration, not a `WeakAny`
definition) so the system linker reports it natively. Sites to review:
`codegen/llvm/backend_core.rs:1051-1072` (`WeakAny` for bodied functions;
`:1461` already notes "Declarations (no body) must have External linkage, not
WeakAny") and the Cranelift `Preemptible` equivalents in
`codegen/common_backend.rs`.

Also unfixed and separate: `check_no_fake_rt_stubs`'s `starts_with("rt_")`
filter still leaves non-`rt_` symbols that *do* reach `nm -u` to be fabricated
by `gen_stub_code` with a `return 0` body. Closing that requires teaching
`real_runtime_defined_symbols()` about libc/system libraries first; see "Why the
`rt_` prefix filter exists" above.

## Related but separate

`scripts/check/check-extern-registration.shs` (report-only) gates the
*declaration* side. This bug is the *link* side.
