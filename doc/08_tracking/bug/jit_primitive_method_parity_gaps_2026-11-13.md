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

## Still OPEN (explicit `pending` rows in the spec)

1. **`i64.to_hex` (and `to_bin`/`to_oct`)** — JIT has no int->radix-text runtime
   helper; fixing needs a new `rt_*` symbol with a C twin (rt dual-implementation
   ratchet). Pure MIR: unresolved.
2. **`print d.get(k)`** — interpreter prints the bare value (`1`); JIT prints
   `Option::Some(<undecoded payload>)`. The Dict.get optional representation differs
   between engines (flat raw vs tagged); needs an owner decision on which shape
   `Dict.get` returns before either engine changes.
3. **Pure MIR `Option.or` / `Option.ok_or`** — still "unresolved method call" when the
   receiver is an `Option<i64>` local; not fixed in this lane.

No pure-Simple full-CLI binary is deployed on this host, so pure-MIR fixes are
verified at the lowering level only (no diagnostic, no `rt_panic` placeholder).
