# Integer 3 boxed into a `T?` slot becomes None; a narrowed scalar optional is used as its handle; extern results folded depending on lowering order

**Status:** source fixes on `work/rel-optional-scalar-static-some-20261011`.
NOT verified natively (needs a rebuilt stage 2); verified by lowering-shape
and executed-MIR specs under the seed.
**Engines:** staged-native, both backends. The interpreter is the oracle.
**Parents:** `native_scalar_nil_compare_payload_bits_2026-10-10.md` (the
series landed as PR #2915), `method_call_optional_param_arg_not_boxed_2026-10-11.md`.
**Found by:** review of the method-call boxing follow-up (probes in
`C:/dev/simple-bootstrap-storage/intensive-tests/review_lowering_followups/`).

Three defects, all in `src/compiler/50.mir`.

## 1. `take(3)`, `w.put(x + 1)`, `val o: i64? = 3`, `return 3` box the integer 3 as None

`ensure_option_handle` fixes the discriminant statically (Some) only when
`local_is_provably_scalar_payload` holds, and that proof was: a registered
scalar HIR type on the local, or a non-I64 scalar MIR slot. A literal, an
arithmetic result, a negation, a cast, an `if` / `??` result and an untyped
local bound from one of those live in an I64 temp with NO registered type, so
they fell through to `normalize_option_handle`, which classifies the word at
RUNTIME: `word == 3` -> None. The integer 3 is that word. This is the original
defect of the parent record (`== nil` true for 3) moved to the boxing site;
bool and float literals escaped only because their MIR slot is not I64.

**Fix.** `hir_expr_is_static_scalar` (structural, no type annotation needed)
recognises expressions that are a non-optional scalar by construction, and
`lower_expr` records their result local in `static_scalar_locals` (propagated
through `val` / `var` copies and assignments like `extern_result_locals`).
`local_is_provably_scalar_payload` accepts a marked local.

| source of the value flowing into `T?` | before | now | why |
|---|---|---|---|
| integer / float / bool literal | runtime (int), static (bool, float) | **static Some** | literal |
| `x + 1`, `1 * 3`, `-x`, `~x`, shifts, bit ops | runtime | **static Some** | an arithmetic result is never nil |
| `x == 1`, `<`, `not x` | static (Bool slot) | static Some | |
| `x as i64` (cast to a scalar type) | runtime | **static Some** | |
| `if c: 1 else: 3`, if-chain with `else`, block, `a ?? 3` (every result static) | runtime | **static Some** | structural, depth-bounded (4) |
| `val n = x + 1; take(n)` (untyped local bound from the above) | runtime | **static Some** | marker copied at the binding |
| `xs[i]` on a local DECLARED `[T]` / `[T; n]`, scalar `T` | runtime | **static Some** | same static element type the `== nil` fold uses |
| param / annotated local / field / user call or method result with a declared scalar type | static | static Some | registered HIR type (unchanged) |
| annotated binding `val o: i64? = <any of the above>`, `return` / tail of `-> T?` | as the source | as the source | same `ensure_option_handle` |
| nil literal | static None | static None | |
| already-Optional local (`T?` param, annotated, Optional call result) | passed through | passed through | never wrapped twice |

Sources that REMAIN runtime-classified, and why that cannot be closed without
a representation change:

| source | why it stays ambiguous |
|---|---|
| extern call result (`-> i64`) | the runtime uses the nil word for "absent" (`rt_enum_payload` on a payload-less variant); the word 3 from an extern may be nil or three, and only the extern knows |
| untyped parameter / untyped local of unknown origin, lambda result, indirect call | no static type: the word may be an Option handle, the sentinel or a payload |
| `Dict` read `d[k]`, `d.get(k)` | a miss returns the nil word in the value slot of a `Dict<K, i64>` |
| builtin method result (`xs.len()`, `s.to_i64()`, `s.index_of(..)`, ...) | lowered to a runtime call into an I64 temp with no registered type; total ones (`len`) could be whitelisted per method -- not done here, a `len()` of exactly 3 is still None |
| `a and b` / `a or b` on non-bool operands | may yield an operand |
| `if` / `match` whose arm is not itself static (e.g. an arm that is a call) and the checker left no type | only the structural proof is available on the flat path |
| char literal | not recognised by this harness' frontend path as `CharLit`; unverified |
| a `var` re-assigned from an ambiguous source inside a loop AFTER a use | the marker is flow-insensitive in lowering order, like `nil_locals` / `extern_result_locals` |

In every remaining case a value that is the integer 3 at runtime is boxed as
None. Closing it needs a nil sentinel that is not a valid payload word in a
raw i64 slot (i.e. scalars tagged or optionals carried as a pair), which is a
representation change, not a lowering fix.

## 2. A narrowed scalar optional was used as its HANDLE

Since the series, an Optional value is always the Option handle. Inside
`fn f(v: i64?) -> i64: if v != nil: return v + 1` the `v + 1` lowered to a raw
add on the parameter local, i.e. on the handle word (executed MIR:
`f(5)` = handle + 1; the interpreter answers 6). Only `if val x = v` and
`v ?? d` unwrapped. Measured before the fix: `v + 1`, `2 * v`, `g(v)` into an
`i64` parameter, `return v` / tail `v` from `-> i64`, `val x: i64 = v` all
used the handle; `v == 3` compared the handle with 3 (always false).

**Fix.** `option_scalar_payload_of(local)` returns the unwrapped payload
(`rt_unwrap_or_self`, the unwrap `??` / `if val` already use, then the
float bitcast / narrow cast that mirrors the boxing) when the local's
registered type is `Optional(<scalar>)`, and the local itself otherwise. It
is applied at every place a plain scalar is required:

- operands of every binary operator except `==` / `!=` (and `and` / `or`,
  which have their own lowering);
- `o == x` / `o != x` with `o` a scalar Optional local and `x` a provably
  plain scalar: `rt_is_some(o) & (payload == x)` (negated for `!=`), so None
  is not equal to the integer 3;
- an argument whose declared parameter is a plain scalar (free-function path
  and `lower_method_call_arg`);
- `return v` and the implicit tail of a function returning a plain scalar;
- `val x: T = v` with a plain scalar `T`.

No flow analysis: the unwrap does not depend on a preceding nil test. Using a
None there yields `rt_unwrap_or_self(None)` (the nil word) where the
interpreter raises -- the same as every other unchecked unwrap.

Closure exposure, counted before choosing a fix over a diagnostic (text scan
of src/compiler, src/lib, src/app: variables annotated `T?` with scalar `T`,
or bound from a function all of whose definitions return a scalar optional,
then used in arithmetic / ordering / indexing / `==` with a non-nil operand
without `!`, `??`, `.unwrap()`, `if val`): **5 uses** -- `src/compiler/30.types/
dim_constraints.spl:309` (`product != value`, `value` from `try_eval -> i64?`)
and `src/lib/nogc_sync_mut/test_runner/test_runner_mcdc_report.spl:550,553,
560,563` (`xs[runtime_id]`). Population: 67 annotated scalar-optional params
/ locals and 85 scalar-optional fields in the three trees. Field reads
(`self.count + 1` with `count: i64?`) are not in the scan.

Not covered: an Optional local used as an array INDEX (`xs[v]`), stored into
a plain scalar FIELD, assigned to an existing plain scalar `var`, interpolated
in a string, or tested for truthiness (`if flag:` with `flag: bool?`).

## 3. `ext() == nil` was folded, and `take(ext())` boxed statically, depending on lowering order

The series excludes extern results from the scalar fold and from static-Some
through `extern_fn_symbols`. That set was filled by the lowering loop when it
REACHED the extern's declaration, and functions are lowered in name order, so
a caller whose name sorts before the extern saw an unmarked symbol: its
`-> i64` result was a "declared scalar", `ext() == nil` folded to `false` and
`take(ext())` boxed a possible nil word as Some. Measured on the landed tree:
`fn a_first(): take(ext_now())` -> static; `fn k_extern()` (sorts after
`ext_now`) -> runtime. The 19 parser sites of the parent record
(`rt_enum_payload(..) == nil` / `rt_tuple_get(..) == nil` in `parse_*`
functions, which sort before `rt_*`) are exactly this shape, so their nil
tests are folded away in a compiler built from the landed series.

**Fix.** Externs are marked in the module prescan, before any body is lowered
(`_MirLowering/module_lowering.spl`).

Still open: an extern declared in ANOTHER module and imported is not in the
calling module's function list, so it is not marked at all there.

## Specs

- `test/01_unit/compiler/mir/optional_scalar_static_some_spec.spl` (11): shape
  per source kind (static vs runtime), the extern order case for both the box
  and the `== nil` fold, and EXECUTED examples -- `take(3)` = 3, `take(0)`,
  `take(x + 1)` with x = 2, `takeb(true)` / `takeb(false)` present, nil
  absent, `val o: i64? = 3`, `w.put(3)`, `w.put(x + 1)`, `w.put(nil)`;
  `v + 1`, `2 * v`, `v > 4`, `g(v)`, `return v`, tail `v`, `val x: i64 = v`,
  `v == 3` / `v != 3` for Some(3), Some(5) and None. 9 of 11 fail on the
  unfixed sources (`take(3)` returned the absent marker; `v + 1` returned
  handle + 1).
- `test/01_unit/compiler/mir/method_call_optional_arg_handle_spec.spl`: its
  literal examples only counted `rt_enum_new` and passed for the
  runtime-classified shape; `boxes()` now reports that shape as -2, so they
  prove a fixed discriminant (4 of 7 fail on the unfixed sources).

How the executed examples work, and their limit: the MIR interpreter has no
runtime library (an unknown callee yields 0), so `rt_enum_new`, `rt_enum_id`,
`rt_is_none`, `rt_is_some` and `rt_unwrap_or_self` are modelled in Simple
source, lowered by the same lowering and bound under those names (handle =
2^60 + payload * 2 + discriminant; nil = the word 3). They prove the lowered
control and data flow, for small non-negative integer and bool payloads; they
do not exercise the real runtime, floats, or either native backend.
