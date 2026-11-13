# Seed JIT / pure-Simple MIR disagree with the interpreter on primitive builtin methods

- **Date:** 2026-11-13
- **Status:** verification-pending (seed + pure-MIR fixes landed by work/jit-parity-20261113; two rows remain OPEN, see below)
- **Severity:** Medium — the JIT either aborted ("Function 'i64.is_even' not found") or
  silently printed a wrong value; the pure-Simple MIR raised a FATAL unresolved-method
  lowering error.
- **Spec:** `test/01_unit/compiler/jit_parity/primitive_method_parity_spec.spl`
  (JIT vs interpreter, via `simple run` with `SIMPLE_JIT_STRICT=1`),
  `test/01_unit/compiler/jit_parity/numeric_parity_mir_lowering_spec.spl` (pure MIR)
- **Out of scope:** integer `max`/`min`/`clamp`/`abs` (separate lane:
  `int_max_min_method_unresolved_in_jit_2026-11-13.md`).

## Audit

98 one-method probe programs over i64/i32/u8/u64, f64, bool, text, `[T]`, Dict and
Option, each run under `SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1` and
`SIMPLE_EXECUTION_MODE=interpret`; 85 agreed, 13 differed (`i64.hash` fails in both
engines, so it is not a parity gap).

| Method | Interpreter | Seed JIT (before) | Pure MIR (before) | Fix |
|---|---|---|---|---|
| `i64.is_even/is_odd/is_zero/is_positive/is_negative` | bool | `Function 'i64.is_even' not found` | unresolved (fatal) | seed: inline Cranelift (`compile_scalar_parity_method`) + HIR BOOL stamp; pure: `try_lower_numeric_parity_builtin` |
| `i64.sign` / `signum` | -1/0/1 | not found | unresolved | same |
| `i64.pow(n)` | 81 | not found | unresolved | seed: square-and-multiply loop; pure: `MirBinOp.Pow` |
| `f64.is_nan/is_finite/is_infinite` | bool | not found | unresolved | seed: `fcmp`; pure: self-equality |
| `text.parse_int()` printed | `Option::Some(123)` | strict JIT refused module (`rt_opt_i64_to_string` unresolved); after resolving it printed `Option::Some(984)` (tagged value fed to the raw renderer) | lowers | `#[no_mangle]` reattached to `rt_opt_i64_to_string` (it was detached onto the wrong item), explicit JIT address entries for the `rt_opt_*_to_string` family, and print renders `parse_*` with the tagged renderer |
| `[T].reduce(init, f)` / `fold` | 6 | `Array.reduce` not found | lowers | cranelift arm -> existing `rt_array_reduce` |
| `var a; a.insert(i, x)` | mutates `a` | spliced copy dropped (`a` unchanged) | lowers | MIR writes the result back to a local receiver |
| `Option.or(other)` | 2 | `Option.or` not found | unresolved | cranelift: `select(rt_is_some, recv, other)` |
| `Option.ok_or(e)` | `Ok`/`Err` | `Option.ok_or` not found | unresolved | cranelift: `rt_enum_new` Ok/Err + select |

## Closed by work/jit-parity2-20261113

- **`i64.to_hex`** (all integer widths): new `rt_i64_to_hex` (Rust `io_print.rs` +
  C twin `runtime_native.c`, registered in `runtime_symbols.rs`, `runtime_sffi.rs`,
  `elf_utils.rs`); seed JIT arm in `compile_scalar_parity_method` + HIR STRING stamp;
  pure MIR lowers it to the same helper in `try_lower_numeric_parity_builtin`. The
  interpreter already had it (`format!("{:x}", n)`). `to_bin`/`to_oct` are not
  covered and were not audited rows.
- **Pure MIR `Option.or` / `Option.ok_or`**: `lower_option_or_builtin`
  (`builtin_method_extras.spl`), dispatched from the Option-receiver probe in
  `method_calls_literals.spl`; `ok_or` results are typed `Result<T, E>` so a chained
  `.is_ok()` resolves. Rows in `numeric_parity_mir_lowering_spec.spl`.

## Still OPEN (explicit `pending` row in the spec): `print d.get(k)`

The interpreter prints the bare value (`1`); the JIT prints
`Option::Some(<undecoded payload>)`. The engines disagree on what `Dict.get` returns.
**This needs an owner decision.** Neither engine was changed.

- **Option A: `Dict.get` returns a real tagged `Option<V>` everywhere.** The
  interpreter prints `Option::Some(1)` / `Option::None`, the same as
  `text.parse_int()` already does (see the audit row above). The JIT keeps its tagged
  shape and only fixes the payload decode in its print path. Cost: every interpreter
  caller that relied on the bare value (`print d.get(k)`, `if d.get(k) == 1`) changes
  output or needs `?? / unwrap`.
- **Option B: `Dict.get` returns flat `V`-or-nil.** The JIT unwraps to the raw payload
  and prints the bare value, matching today's interpreter. Cost: `get` stays the one
  `V?` method whose value is not an Option. That conflicts with the
  nil-only-in-unsafe / `None`-in-safe-code rule (ADR-006 panic-free safe code).

**Recommendation: Option A.** The signature is `V?`. `parse_int` already settled
that an Option prints as `Option::Some(..)`. Safe code is meant to see `None`, not
nil. Fix the JIT payload decode first, which is a pure bug either way, then move the
interpreter in a separate change with a census of `d.get(` print/compare sites.

No pure-Simple full-CLI binary is deployed on this host, so pure-MIR fixes are
verified at the lowering level only (no diagnostic, no `rt_panic` placeholder).
