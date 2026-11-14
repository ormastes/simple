# Native Option -> integer sink: a MISS reads as 3, and a stored 3 reads as None

- **ID:** `native_option_int_sink_miss_and_payload_three_2026-11-07`
- **Severity:** P1 (silent wrong value)
- **Status:** Defect 1 fixed in source (MIR, rt_unwrap_or_trap at scalar sinks, 2026-11-07), native confirmation pending; Defect 2 fixed in source (MIR, 2026-11-07), native confirmation pending a Stage 2 rebuild
- **Layer:** `src/compiler/50.mir` integer sinks + runtime `rt_unwrap_or_self`
- **Follow-up of:** `native_list_any_get_i64_sink_returns_option_handle_2026-11-07`

## Defect 1 — MISS into an i64 sink is a silent 3

`fn f(w: [i64], i: i64) -> i64: w.get(i)` with `i` out of range (and the same
for `w: list` after the 2026-11-07 sink fix): the integer sinks unwrap through
`rt_unwrap_or_self` (`src/runtime/runtime_native.c:6269`,
Rust twin `objects.rs:530`). The None handle carries payload 3, and
`rt_unwrap_or_self` returns that payload, so the caller sees `3` with no
diagnostic. The interpreter's behaviour on a miss into a declared i64 is not
a valid integer either. Present for typed `[i64]` since the scalar-sink unwrap
landed (`optional_scalar_runtime_classified_three_becomes_none_2026-10-11`).

**Proposal:** at implicit-tail / `return` / `val y: i64 =` integer sinks
(`option_scalar_payload_of` and `option_payload_for_int_sink` in
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`), emit
`rt_unwrap_or_trap` (already declared at `src/runtime/runtime.h:940`) instead
of `rt_unwrap_or_self`, for both typed scalar and `Optional(Any)` inners, so a
None reaching a non-optional integer slot traps loudly. `??`, `if val` and
`.unwrap_or` keep their own paths. Needs native verification after a Stage 2
rebuild; check the trap symbol is backed on every lane before switching.

## Defect 2 — a stored element 3 is classified None (fixed in source)

`lower_array_first_or_last` normalized the decoded element through
`ensure_option_handle` -> `normalize_option_handle` (runtime Some check:
already a handle -> unchanged, word 3 -> None, else Some). The element is
int-decoded first, so a stored `3` became the word 3 and was classified
**None**: `w.get(0)` with `w = [3]` read as a miss (`?? -1` gave -1).

Correction to the first version of this record: the typed `[i64]` path is
affected too. The decoded element is a fresh cast temp with no HIR type, so
`local_is_provably_scalar_payload` falls to the I64-slot check and returns
false; the MIR for `fn f(w: [i64], i: i64) -> i64: w.get(i) ?? -1` has the
same `rt_enum_id` + `option_norm_raw` (`word == 3`) shape as `list`.

Native probe on the pre-fix Stage 2 binary
(`simple-phase3/build/bootstrap-phase3-1/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple`,
`SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 native-build --backend=cranelift`,
same with `SIMPLE_BOOTSTRAP_SKIP_MIR_OPT=1`):

| shape | native | expected |
|---|---|---|
| `w: list`, w = [4], `w.get(0) ?? -1` | 4 | 4 |
| `w: list`, w = [3], `w.get(0) ?? -1` | **-1** | 3 |
| `w: [i64]`, w = [3], `w.get(0) ?? -1` | **-1** | 3 |

**Fix:** the some-arm is reached only after the bounds check, so its payload
is present by construction. It now builds Some with a compile-time
discriminant through `emit_option_handle_with_disc`
(`_MirLoweringExpr/switch_operators_calls.spl`, hoisted out of
`ensure_option_handle`, which still calls it). Boxed payloads
(`option_payload_is_boxed`) and `Optional` elements keep the runtime path:
the sentinel cannot collide for a boxed handle, and a stored Option handle
must not be wrapped again. Only a concrete scalar element
(Int/Float/Bool/Char) is fully static. An `Any` or type-parameter element
may itself be a stored Option handle (`rt_value_as_int_wide` passes heap
handles through), so it goes through `normalize_present_option_handle`:
an enum-id-1 handle passes through unchanged (as the interpreter returns a
stored Option), anything else, including 3, is Some. Only the `== 3` test
is dropped. (Review finding on the first version, which made every `Any`
element static and so turned a stored Some(x) into Some(Some(x)).)

**Evidence:** `test/01_unit/compiler/mir/list_any_get_scalar_sink_unwrap_spec.spl`
case "does not test the element word against the nil sentinel for list and
[i64]" (no `option_norm_raw`): red before the fix (5/6), green after;
case "passes a stored Option handle through for Any and type-parameter
elements" (`option_present_handle` present for `list` and `[T]`): red on the
first version (6/7), green after (7/7). Neighbours unchanged before/after:
`null_coalesce_lowering_spec` 0/2, `optional_scalar_handle_representation_spec`
4/5, `optional_scalar_static_some_spec` 17/18 (same failing examples),
`if_val_payload_interp_type_spec` 4/4, `array_at_native_lowering_spec` 10/10,
`method_call_optional_arg_handle_spec` 7/7, system
`null_coalescing_try_operator_spec` 15/15. Expected after a Stage 2
rebuild: the probe prints 3 for both `[3]` rows.

**Still open, same collision one level up:** `if val v = opt` is
parser-desugared to a binding plus `v != nil`, and the MIR compares the
unwrapped payload with 3 (`exists_check_merge` in
`_MirLoweringExpr/expr_dispatch.spl` `.?` lowering), so
`if val v = [3].get(0)` still skips its branch after this fix (read off the MIR, not run natively). Not changed
here: it is the desugar's representation, shared by every scalar Optional.

## Related limit

`option_payload_for_int_sink` assumes an int-decoded payload. That holds only
for the array get/at/first/last producer. Other `Optional(Any)` producers
(`any?` params, tagged raw-probe dict reads) carry a tagged word, so the sink
returns the tagged word rather than the value. The limit is documented in the
helper's docstring.

## Defect 1 fix (2026-11-07, lane u-optsink)

`option_payload_for_int_sink` now unwraps through `rt_unwrap_or_trap` for
both the typed scalar and the `Optional(Any)` inner (new
`option_scalar_payload_via(local, symbol)`). `option_scalar_payload_of`
keeps `rt_unwrap_or_self`, because its Eq / arithmetic callers read the
payload even on None (`lower_scalar_optional_eq_*` mask it with
`rt_is_some`/`rt_is_none`). `rt_unwrap_or_trap` is backed on the C runtime
(`runtime_native.c`) and the Rust seed (`objects.rs`).
Spec: `test/01_unit/compiler/mir/option_int_sink_miss_traps_spec.spl` (red
2/3 before, green after); `list_any_get_scalar_sink_unwrap_spec.spl` updated
to the trap symbol. Still required: a Stage 2 native run showing a MISS into
`-> i64` aborts with ".unwrap() called on None".

## Re-verification 2026-11-14 (origin/release/1.0.0 bc9b18b3106)

Defect 1 is fixed in source and nothing more was changed. `option_payload_for_int_sink`
emits `rt_unwrap_or_trap` (`switch_operators_calls.spl:975`), and all three
integer sinks route through it: the tail return (`function_lowering.spl:1173`),
`return` (`expr_dispatch.spl:3786`) and `val y: i64 =` (`mir_lowering_stmts.spl:1450`).
`rt_unwrap_or_trap` is backed in `runtime_native.c:21491` (it aborts with
`.unwrap() called on None`) and in `objects.rs:622`. The seed
(`seed-try-target/release/simple test`) runs
`list_any_get_scalar_sink_unwrap_spec` 7/7 and `option_int_sink_miss_traps_spec` 2/2.

Interpreter reference (`SIMPLE_EXECUTION_MODE=interpret`, the same seed), a MISS on `[10, 20].get(5)`:

| sink | interpreter | native after the fix |
|---|---|---|
| tail `w.get(i)` with `-> i64`, both `[i64]` and `list` | raises `nil is forbidden by the non-optional return contract` | traps |
| `return w.get(i)` | raises (same) | traps |
| `val y: i64 = w.get(i)` | **binds `y = nil` and does not raise**; `y + 1` gives 1, and only a later `-> i64` return raises | traps at the binding |
| `w.get(i) ?? -1` | -1 | -1 (unchanged) |

Open divergence: the interpreter does not enforce a declared `i64` annotation on
`val` against nil. Native is now stricter, and the interpreter is the side that
should move. That is a separate interpreter item and is not changed here. The
default seed `run` (JIT) still prints `ret=0` / `list=3` on a miss. That is the Rust
seed's own JIT, not this MIR lowering.

Still pending: a Stage 2 native run that shows the abort.

## Native RED on the pre-fix run-15 Stage 2 (2026-11-14)

Binary: `simple-bootstrap/build/bootstrap-opus-15/stage2/aarch64-unknown-linux-gnu/simple`
(mtime 2026-11-07 10:01 KST, `source_snapshot_sha256=01f2a519...` in its
`bootstrap-preflight.env`; the u-optsink lane started 2026-11-07T06:57Z =
15:57 KST, so this binary predates 330262efe86). Command:
`SIMPLE_PROJECT_ROOT=<repo> SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1 native-build f.spl -o f.bin`,
`w = [10, 20]`, calls with i=1 then i=5:

| fixture | native (run-15) | expected after the fix |
|---|---|---|
| `fn ret_typed(w: [i64], i: i64) -> i64: return w.get(i)` | `hit=20`, **`miss=3`**, rc 0 | `hit=20`, then abort `.unwrap() called on None` |
| `fn tail_list(w: list, i: i64) -> i64: val x = w.get(i); x` | `hit=212553838455681`, `miss=212553838460065` | `hit=20`, then abort |

The `list` row shows the predecessor bug
(`native_list_any_get_i64_sink_returns_option_handle_2026-11-07`, also fixed
after run-15), recorded as observed. Both `return` and tail sinks raise in the
interpreter (table above), so the native trap matches it.

**GREEN still pending.** A Stage 2 rebuild from release/1.0.0 was not run: the
host had 6.3 GB disk and 27 GB RAM available (thresholds 20 GB / 30 GB). Still
required: rebuild Stage 2, then the two fixtures above must print `hit=20` and
then abort on the miss.
