# Native `list.get(i)` into an `i64` sink returns the Option handle pointer

- **ID:** `native_list_any_get_i64_sink_returns_option_handle_2026-11-07`
- **Severity:** P1 (silent wrong value, no diagnostic)
- **Status:** fixed in source (MIR); native confirmation pending a Stage 2 rebuild
- **Layer:** `src/compiler/50.mir` (pure-Simple native lowering)
- **Found on:** self-hosted Stage 2 built from release/1.0.0 `4ff1e3b51f5`
  (`simple-phase3/build/bootstrap-phase3-1/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`),
  `SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 native-build --backend=cranelift`.

## Repro

```simple
fn list_get(w: list, i: i64) -> i64:
    val x = w.get(i)
    x

fn main() -> i64:
    var w = []
    w.push(4)
    print "lg={list_get(w, 0)}"   # native: lg=200634408607585 (varies per run); seed interpreter: lg=4
    0
```

Measured on the Stage 2 binary above (probe `build/probe/lg2.spl` in the fix worktree):

| shape (`w: list`, w = [4]) | native result | expected |
|---|---|---|
| `val x = w.get(0); x` from `-> i64` | 188619666521953 / 204136411196289 (handle ptr, ASLR) | 4 |
| `return w.get(0)` from `-> i64` | 208320240151425 | 4 |
| `val y: i64 = w.get(0); y` | 208320240151425 | 4 |
| `val y: i64 = w.get(0) ?? -1` | 4 | 4 |
| `if val v = w.get(0): v + 1` | v=0, 1 | v=4, 5 (**separate, still open**, see below) |
| `[i64]` receiver, `val x = w.get(1); x` | 8 | 8 |

## Root cause

- HIR lowers `list` to `Array(Any)` (see `array_get_contract_drift_crypto_2026-10-18`).
- `lower_array_first_or_last` (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:6957`)
  accepts an `Any` element, decodes it with `lower_type(Any) = i64`
  (`rt_value_as_int_wide`), and returns a real `Optional(Any)` handle.
- The integer sinks — implicit tail (`_MirLowering/function_lowering.spl:1151`),
  explicit `return` (`_MirLoweringExpr/expr_dispatch.spl:3646`) and an annotated
  `val y: i64 =` binding (`mir_lowering_stmts.spl:1301`) — call
  `option_scalar_payload_of` (`_MirLoweringExpr/switch_operators_calls.spl:885`),
  which unwraps only when the Optional inner type is a plain scalar. `Any` is not,
  so the handle was returned unchanged and `local_needs_erased_decode` does not
  fire for an `Optional(..)` HIR type: the enum handle pointer became the i64.
  MIR before the fix: `rt_array_get -> rt_value_as_int_wide -> rt_enum_id/rt_enum_new -> Return` with no `rt_unwrap_or_self`.

## Fix

New `option_payload_for_int_sink(local, sink_type)` beside
`option_scalar_payload_of`: same scalar unwrap, plus, for an `Optional(Any)`
local in an **integer** sink, `rt_unwrap_or_self` and register the raw word with
the sink's scalar HIR type + `static_scalar_locals` (no second decode). Used at
the three sinks above. `option_scalar_payload_of` itself is unchanged (it also
backs `lower_scalar_optional_eq_plain` and operator paths). Float/bool sinks are
not covered: the payload is an int-decoded word there and reinterpreting it
would be wrong.

## Evidence

- Spec `test/01_unit/compiler/mir/list_any_get_scalar_sink_unwrap_spec.spl`
  (real HIR->MIR lowering, run under the seed interpreter):
  red before the fix (1 of 3 failed: no `rt_unwrap_or_self` in tail/return/bind),
  green after (3/3).
- Neighbour specs unchanged versus the unfixed baseline (same pre-existing
  failures before and after): `optional_scalar_handle_representation_spec`
  4/5, `optional_scalar_static_some_spec` 17/18, `null_coalesce_lowering_spec`
  0/2; `50.mir/if_val_payload_interp_type_spec` 4/4.
- **Not verified natively.** The fix only reaches a native binary after a
  Stage 2 rebuild; expected after rebuild: the probe prints `lg=4`, `ann=4`,
  `ret=4`.

## Still open (not fixed here)

- `if val v = w.get(0)` on a `list` binds `v` as `Any` and decodes the
  already-decoded payload a second time (4 -> 0). Root: the producer decodes
  an `Any` element to a raw int while `Any` consumers expect a tagged word.
  Fixing the producer (keep `Any` payloads tagged) changes every `Optional(Any)`
  consumer (`??` currently relies on the raw word) and needs native
  verification; tracked here rather than widened silently.
- **MISS into an i64 sink is still a silent wrong value (pre-existing, unchanged here):** the None handle carries payload 3 and `rt_unwrap_or_self` (`src/runtime/runtime_native.c:6269`, Rust `objects.rs:530`) returns it, so an out-of-range `get` reads as `3`. Same for typed `[i64].get`. A stored element `3` in a `list` is also classified None by the runtime Some check. Both are in follow-up `native_option_int_sink_miss_and_payload_three_2026-11-07`, which proposes `rt_unwrap_or_trap` at integer sinks.
- `option_payload_for_int_sink` assumes an int-decoded payload. That holds only for the array get/at/first/last producer: other `Optional(Any)` producers (`any?` params, tagged dict reads) hand over a tagged word. The limit is stated in the helper docstring.
- The public array `get` contract (Option vs element) remains the open question
  of `array_get_contract_drift_crypto_2026-10-18`.

Related: `jit_tuple_get_returns_raw_tagged_word_to_i64_sink_2026-08-17` (JIT sibling, closed),
`optional_scalar_runtime_classified_three_becomes_none_2026-10-11` (introduced the scalar-sink unwrap).
