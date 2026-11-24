# A float flowing into an int-typed parameter or return: engines disagree

- **Filed:** 2026-11-24
- **Status:** FIXED (branch `work/compiler-float-int-typeerror-20261124`). Owner decision 2026-11-24:
  reject it in the type checker; the program writes `as iN` / `.to_iN()`.
- **Area:** Rust seed type checking, interpreter call/return, and Cranelift uniform i64 ABI
- **Found by:** compiler-numeric-conv2 lane (work/compiler-numeric-conv2-20261124), while
  routing the narrow-slot adapters through `float_to_int_saturating`

## Repro

```simple
fn r32(x: f64) -> i32:
    x
fn take8(v: u8) -> i64:
    v as i64
fn main():
    print("r32 2.5 {r32(2.5)}")
    print("take8 300.5 {take8(300.5)}")
```

Measured 2026-11-24 on aarch64, seed at numconv tip `4a32e48fb62`:

| row | interpreter | JIT |
|---|---|---|
| `r32(2.5)` (float returned from `-> i32`) | `2.5` (no coercion) | `4612811918334230528` (f64 bits) |
| `r32(1e20)` | `100000000000000000000.0` | f64 bits |
| `take8(300.5)` (float passed to `u8`) | `300` (truncated, not narrowed) | `0` |

The program is accepted without any diagnostic. None of the three engines agrees with an
explicit `as` cast (which saturates: 2, 255).

## Cause

The type checker accepts a float where an int-typed parameter or return is declared, but no
engine inserts a conversion:
- The interpreter keeps the float in an int-typed return, and truncates without narrowing
  for an argument.
- The JIT moves values through the uniform i64 slot. A float return keeps its bits (see
  `body.rs` Return lowering). A float argument reaches the callee's int vreg as bits, then
  narrows.

The narrow-slot adapters in `adapt_value_to_type` / `calls.rs` / `body.rs`, now
saturating, only fire for Cranelift-typed narrow slots (runtime/SFFI signatures), not for
these user functions.

## Fix direction

Either reject an implicit float -> int at the call/return site (the user writes `as T`, which
saturates on every engine), or have HIR insert the same saturating cast. Owner decision.

## Resolution (2026-11-24)

**Owner decision:** a float flowing into an integer-typed parameter, or returned
from an integer-typed function, is a TYPE ERROR in the Rust seed's type checker
(HIR lowering). The program must convert explicitly with `as iN` or
`.to_iN()`; both saturate the same way on every engine. int -> float widening
stays implicit (owner decision 2026-11-13). The self-hosted cranelift adapter
is untouched.

**Change** (`hir/lower/module_lowering/function.rs`, `expr/calls.rs`, `expr/mod.rs`):

- `is_float_into_int(expected, found)` holds when `found` is f32/f64 and
  `expected` is i8..u64.
- **Return position:** `hir_types_compatible` no longer treats every numeric
  pair as compatible; a float found for an integer expected is a mismatch.
  This covers implicit tails and explicit `return`, through
  `validate_declared_return_type`. Primitive pairs are hard errors; aggregates
  keep their warning.
- **Argument position:** `reject_float_for_int_slot` runs beside
  `reject_callable_for_enum_slot` at the same call sites. That covers
  free-function calls (including generic functions with a concrete integer
  slot, and calls through a function-typed value) and methods on a class or
  struct declared in the same file. The message is:
  `type mismatch: argument N of `f` is declared as `u8` but receives `f64`; convert explicitly with `as u8` or `.to_u8()``.
- **Not covered:** method calls on receivers declared in another file (no
  resolved parameter list at that HIR site, the same limit as the enum-slot
  check) and erased (`any`) slots.

**What a type error does today:** `bin/simple run` under the JIT reports it,
then falls back to the interpreter, as it already did for every HIR type
error. The interpreter does not lower to HIR, so the program still runs there.
`SIMPLE_JIT_STRICT=1` / `SIMPLE_JIT_STRICT_ALL=1` refuse the fallback. Making
`run` fail on a type error is a separate, pre-existing policy.

**Evidence:**

- Red/green: `compiler/tests/float_into_int_slot_is_type_error.rs`.
  - Rejected: implicit tail, explicit `return`, float-literal tail, free-function argument, a nested `f64` call result, an `f64` local, a method argument, a generic function's concrete `i64` slot, and a call through `fn(i64) -> i64`.
  - Still compiles: int -> f64 argument and tail, `as u8` / `as i32`, `.to_i64()`, a generic `T` slot taking a float, and int/float into matching slots.
- Tree sweep: every `.spl` under `src/`, `test/` and `examples/` (48,515 files) was lowered per file with `lower_with_context`.
  - **10 call sites in 2 files** now error, all in `src/app/{coverage,stats}/render_adapter.spl`. They passed `(fraction, width)` to `progress_bar(current: i64, total: i64, width: i32)` and `(fraction, css)` to `progress_bar_html(current: i64, total: i64)`, so they were also wrong arity.
  - They now pass the counts each bar takes. The module cannot run on base or head anyway: it imports private functions from `app.ui.render`.
  - After the fix: 0 sites.
  - Limit: ~6,600 files already fail HIR lowering for unrelated reasons, and lowering stops at the first error, so a float -> int site behind another error is not counted.

### Acceptance (2026-11-24)

- **Cargo `--lib` (simple-compiler) is the same test population on both sides.**
  - Lane: 5049 passed, 19 failed. Base `4da62cc1731`: 5052 passed, 16 failed.
  - The tests that failed only on the lane changed between runs: fam_abi, cranelift_sffi jit_runtime_symbols, import memo, sffi_dict scope_read, string_accum. Every one passes 3/3 when run alone with `--exact --test-threads=1`, so they fail only under 8-thread parallel load.
  - The first lane `--lib` run crashed with SIGSEGV before finishing. The two reruns completed without it.
- **Real regression found and fixed:** `pipeline::native_project::object_cache_slice_tests::interface_change_recompiles_dependents_and_keeps_unrelated_cached`.
  - Its `CONS` fixture returned `provide() + p.y` from `-> i64`. In the "field type change" and "return type change" variants that sum is `f64`, which is now correctly rejected.
  - The fixture now writes `(provide() + p.y) as i64`, which is a no-op in the `i64` variants. The test passes 3/3 when run alone.
  - Fixtures embedded in Rust tests were outside the `.spl` tree sweep. The full `--lib` run is what covers them.
- **Integration-test binaries:** every lane failure also fails on base.
- **AOT:** `batch_pipeline` and `native_link` pass on the lane. `native-build` on the seed refuses the Rust fallback, so these cargo AOT tests are the acceptance check.
- **New spec:** `float_into_int_slot_is_type_error` passes 3/3. It failed 2 of 3 at the red commit.
  - The closure case is covered by a call through an `fn(i64) -> i64` value with an `f64`, in the argument-position test.
- **Where the error is fatal:**
  - `SIMPLE_JIT_STRICT=1 simple run repro.spl` exits 1.
  - Plain `run` prints the type error, then `[jit-fallback]` drops the module to the interpreter and exits 0. This fallback policy existed before this change and is unchanged.
  - HIR/native compile paths (`native-build`, the cargo AOT tests) fail hard.
- **Web pages:** 8 pages at 1x and 4x give JIT == interpreter, byte-identical to base, with 0 jit-fallbacks.
