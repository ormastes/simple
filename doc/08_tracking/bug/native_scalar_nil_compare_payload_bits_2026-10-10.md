# Native: `v == nil` is true for the integer 3 (both backends) and for bool `true` (LLVM) on non-optional scalars; scalar optionals lose nil through unboxed producers

**Status:** source fixes on `work/rel-native-nil-compare-20261010` (commit
series on top of `7725bd9efb5`); they take effect only in a REBUILT stage 2
and are NOT yet verified natively (see "Verification on the next rebuild").
**Engines:** staged-native (stage 2 and later), `--backend llvm` and
`--backend cranelift`; also the seed's default JIT `run` lane. The tree-walk
interpreter (`SIMPLE_EXECUTION_MODE=interpret`) is the oracle.
**Found via:** `HirCodecWriter.put_i64` / `put_bool` writing `N` for 3 / true
so the stage-2 HIR cache never hit
(`hir_codec_put_i64_three_encoded_as_nil_native_2026-10-10.md`, codec-only
workaround on a sibling branch).

## Root cause

1. **MIR lowering** (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`,
   Binary `Eq`/`NotEq` fall-through after the Optional/`rt_is_none` routing):
   `nil` is materialized as the raw word **3** (`case NilLit`; `rt_core_nil()`
   = SPECIAL tag 0b011, payload 0). A NON-optional scalar operand was not
   routed anywhere, so the generic `emit_binop(Eq, v, 3)` compared payload
   bits with the sentinel. Same raw test in `??` (`rt_is_some(v)` on payload
   bits) and `.?` (what `if val x = v:` desugars to).
2. **LLVM backend** (`_MirToLlvm/core_codegen.spl` `translate_binop`
   `case Eq/Ne`): the compare ran at the LEFT operand's type; a `bool` param
   is `i1`, so the i64 constant 3 was `trunc`'d to 1 and `true == nil` was true
   while `nil == true` was false. Cranelift keeps Bool as i64 (defect 1 only).
3. **Scalar optionals** (`i64?`, `bool?`, `f64?`, ...): the canonical
   representation is the enum-id-1 handle from `ensure_option_handle`, but
   (a) the discriminant for a scalar payload was chosen purely from compile-
   time provenance (`nil_locals`), so a value of unknown provenance was
   wrapped as `Some(...)` -- an already-boxed `T?` PARAM (registered in
   `local_hir_types` only, never in `option_value_locals`) got wrapped a
   second time at a return/arg/binding, and an extern result / Dict miss
   carrying the raw nil word became `Some(nil)`; (b) the implicit tail
   return of a `-> T?` function (`function_lowering.spl`, the `Any`-only
   boxing arm) returned the raw word: `fn none_bool() -> bool?: nil`
   returned 3, `fn id(v: char) -> char?: v` returned the raw char.

## Semantics (seed interpreter, `SIMPLE_EXECUTION_MODE=interpret`)

The seed answers `false` for `v == nil` on every scalar VALUE (0, 1, 3, true,
false, fields, elements, call results) -- but it is dynamically typed, and
the checker enforces the non-optional contract on RETURNS only
(`30.types/type_infer/inference_expr.spl` `infer_return`). A nil literal
passed to an `i64` parameter, or an untyped call result bound to
`val x: i64`, still carries nil into the slot there, and the seed answers
**true** (`fn f(v: i64): v == nil`; `f(nil)` -> true; `val x: i64 =
untyped_nil(); x == nil` -> true, `x ?? 7` -> 7). Natively that slot holds
the word 3 and can never answer differently from the integer 3. So the fold
is a semantic DIVERGENCE from the seed in exactly those nil-into-scalar
flows, not a representation-independent rewrite. It is made sound by
construction through (i) a checker rule naming those flows so the
declaration becomes `T?`, and (ii) the compiler's own nil-aware scalar
declarations being retyped. Measured divergence table (seed vs. fold):

| flow | seed | fold |
|---|---|---|
| `f(nil)` where `f(v: i64)` | true | false (checker now diagnoses the call) |
| `f(untyped_nil())` | true | false (NOT diagnosed: needs flow typing) |
| `val x: i64 = untyped_nil(); x == nil` / `x ?? 7` | true / 7 | false / 3 (NOT diagnosed) |
| extern `-> i64` result `== nil` | true when absent | runtime compare kept (extern results are excluded from the fold) |

## Native evidence (frozen stage 2 `simple-bootstrap 1.0.0-rc.1`, src @6b540f21546)

Non-optional scalars (`exp` = interpreter):

| line | exp | llvm (before) | cranelift (before) |
|---|---|---|---|
| `i64_eq(0,1,3,11,19)` | `false false false false false` | `false false true false false` | `false false true false false` |
| `i64_eq_rev(3,4)` (`nil == v`) | `false false` | `true false` | `true false` |
| `i32_eq(3,4)` / `u8_eq(3,4)` | `false false` | `true false` | `true false` |
| `bool_eq(false,true)` | `false false` | `false true` | `false false` |
| `i64_ifval(3,4)` | `some(3) some(4)` | `none some(4)` | `none some(4)` |
| `i64_coalesce(3,4)` | `3 4` | `99 4` | `3 4` |
| `ret` (`r3==nil rt==nil ret3()==nil ret_true()==nil`) | `false false false false` | `true true true true` | `true false true false` |
| `field` (`bx.i bx.b bx.f ==nil; bx.i bx.b !=nil`) | `false false false true true` | `true true false false false` | `true false false false true` |
| `elem` (`[1,3,11]`,`[false,true]` `==nil`) | all `false` | `false true false false true` | `false true false false false` |
| `local` (`lit3==nil litt==nil lit3!=nil litt!=nil`) | `false false true true` | `true true false false` | `true false false true` |

Scalar optionals (same binary; `exp` = interpreter; see the probe below):

| line | exp | llvm (before) | cranelift (before) |
|---|---|---|---|
| `param_eq_i64` (`mk(3) mk(0) none() nil 3 Some(3)`) | `false false true true false false` | `false false true false false false` | same as llvm |
| `param_eq_bool` (`mk(true) mk(false) none() nil true`) | `false false true true false` | `false false true false false` | same |
| `param_eq_f64` (`mk(3.0) mk(0.0) nil 1.5`) | `false false true false` | `false false false false` | same |
| `param_eq_i32_u8` (`3 nil 3 nil`) | `false true false true` | `false false false false` | same |
| `identity` (`id(mk(3)) id(nil) ...` x3 types) | `false true false true false true` | all `false` | same |
| `raw_to_opt(3)` `== nil`, `?? 99` | `false 3` | `true 99` | same |
| `ifval` (`mk(3) mk(0) nil 3 ...`) | `some(3) some(0) none some(3) ...` | `none some(0) none none ...` | same (+ f64 payload garbage) |
| `coalesce_i64(nil)` / `coalesce_f64(...)` | `99` / `3.0 9.5` | `99` / `3.0 9.5` | `3` / garbage |
| `exists(nil)` | `absent` | `absent` | `present` |
| `local` (`l3 l0 ln lb lbf lf ==nil`) | `false false true false false false` | same as exp | all `true` |
| `field` (`h.oi h.ob h.of hn.oi hn.ob hn.of ==nil`) | `false false false true true true` | same as exp | all `true` |
| `closure` (`cap==nil capn==nil`) | `false true` | `false false` | `false false` |
| `reassign`, `elem`, `dict`, `try`, `unwrap`, `match` | -- | match exp | `reassign` wrong, rest match |

The cranelift-only `local`/`field`/`exists` rows (annotated `val ov: i64? = 3`
reads as nil) are consistent with the reviewer's lead: `lower_type(Optional)`
is `Tuple([Bool, T])` while the value is an i64 handle, and cranelift maps a
Tuple to PTR. NOT fixed here; re-measure on a stage 2 built from this source
(the `Some(x)`/param boxing and tail-return fixes change what reaches it).

## Fix (commit series)

1. `nil_compare_operand_is_plain_scalar` (expr_dispatch.spl): `v == nil` /
   `v != nil` (both orders), `v ?? d` and `v.?` on a STATICALLY non-optional
   primitive scalar (HIR Int/Float/Bool/Char from the checker annotation or
   the declared-local registry; MIR scalar local; not an Option handle, nil
   literal, tagged runtime value, or an EXTERN call result) fold to the
   constant / the value. Optional, text, enum, struct, untyped and extern-
   result operands keep `rt_is_none`/`rt_is_some`/`rt_native_eq`.
2. `equality_compare_type` (core_codegen.spl): Eq/Ne with an i1 left and a
   wider integer right compares at the integer's width (zext).
3. Retyped nil-aware scalar declarations to optionals: `HirCodecWriter.put_i64
   (v: i64?)` / `put_bool(v: bool?)`, `hc_i64_key_before_v1(left: i64?,
   right: i64?)`, `StateVariant.suspension_point_id: i64?`.
4. Checker rule (`_subsume_fallback`, inference_expr.spl): a nil literal or
   an Optional-typed value flowing into a non-optional scalar parameter /
   annotated binding is diagnosed ("... cannot flow into the non-optional
   scalar type 'i64'; declare ... as 'i64?'"), mirror of the return rule.
   Warn-first: the driver's typecheck pass is Advisory by default
   (`SIMPLE_TYPECHECK_PROFILE`). Measured gaps: `y = nil` on a declared
   `var y: bool` and `Box(i: nil)` into an `i: i64` field are not caught (the
   Assign arm checks against the synthesized scheme instance; struct-literal
   fields are not checked against declared field types). The seed needs the
   same rule (it has only the return rule) -- filed below.
5. Representation rule for optionals, enforced in `ensure_option_handle`
   (switch_operators_calls.spl): an Optional value is ALWAYS the enum-id-1
   handle or the bare nil sentinel; a raw payload word never stands for an
   Optional. Discriminant fixed statically only for a nil literal (None) or
   a provably non-optional scalar source (Some: registered scalar HIR type,
   or a non-I64 scalar MIR slot); an already-Optional local (declared `T?`
   param, registered Optional) passes through unwrapped; everything else is
   classified at runtime by `normalize_option_handle` (`rt_enum_id == 1` ->
   unchanged, `== 3` -> None, else Some). The implicit tail return of a
   `-> T?` function now goes through the same promotion
   (function_lowering.spl). Consumers (`== nil`, `!= nil`, `if val`, `??`,
   `.?`, `.unwrap()`, postfix `?`, `case Some/nil`) already use the handle
   predicates (`rt_is_none`/`rt_is_some`/`rt_enum_discriminant`/
   `rt_unwrap_or_self`).

Specs (interpreted; fail-before / pass-after unless noted):
`test/01_unit/compiler/mir/scalar_nil_compare_folds_to_constant_spec.spl`
(5), `test/01_unit/compiler/backend/llvm_bool_int_equality_width_spec.spl`
(2), `test/01_unit/compiler/hir/hir_codec_nil_scalar_optional_spec.spl` (4:
`put_i64(nil)`->`N`, `put_i64(3)`->`3`, key order), `test/01_unit/compiler/
types/nil_into_scalar_slot_check_spec.spl` (4), `test/01_unit/compiler/mir/
optional_scalar_handle_representation_spec.spl` (5: 6 scalar types x
producers {return, binding, call-arg, field, nil literal, extern/untyped} x
consumers {`== nil`, `!= nil`, `if val`, `.?`, `unwrap`, `??`, `?`, match}).
Neighbouring specs `null_coalesce_lowering_spec`, `optional_float_nil_compare
_lowering_spec`, `option_return_boxing_paths_spec`, `local_mir_type_nilable_
contract_spec`, `hir_codec_roundtrip_spec` (3/4), `hir_codec_key_order_v1_spec`
(2/6), `hir_codec_writer_audit_v1_spec` (1) are red IDENTICALLY on the
unmodified base (measured by checking out the original files) -- pre-existing.

## W-nil-compare: sites that relied on a typed scalar carrying nil

Direct scalar-typed param/local `== nil` in `src/compiler`: 5 sites, all HIR
codec, all retyped in this series. Call sites that nil-test a scalar-returning
function (`f(...) == nil`, `if val x = f(...)`; heuristic scan over
src/compiler, src/app, src/lib): 38, e.g. `20.hir/hir_types.spl:510,547,566`
(`get -> i32`), `80.driver/cache/cas_batch_transaction.spl:63`
(`rt_file_read_regular_no_follow_bounded -> i64`, extern: still a runtime
compare), `90.tools/coupling/layer_check.spl:23-31` (`extract_layer_number
-> i64`), `src/app/office/mod.spl:1316,1459,1462,1529` (`parse_range ->
i64`), `src/lib/js/builtins/json.spl:43` (`parse_f64 -> f64`),
`src/lib/nogc_sync_mut/diag.spl:258,334,355` (`get -> i32`),
`src/lib/nogc_sync_mut/play/wm/mod.spl:260,354,381` (`to_i64 -> i64`),
`src/lib/blink/style/cascade.spl:149,249` (`parse_color_value -> u32`, `if
val`). Functions declared `-> <scalar>` whose body has a bare `nil` return
line: 2088 (heuristic; top files `tooling/easy_fix/rules.spl` 57, `90.tools/
fix/rules/impl_/lint_short_grammar.spl` 57, `40.mono/monomorphize/
deferred_deserialize.spl` 54, `95.interp/mir_interpreter.spl` 39). The
checker's return rule rejects `-> i64: nil` only when it can type the tail;
these are the declarations that should become `T?`. Not mass-edited. The 14
parser sites comparing `rt_enum_payload(...) -> i64` with nil
(`10.frontend/parser_types_expr.spl:83-267`, `parser_types.spl:449,458`) are
EXTERN results and keep the runtime compare (fix 1).

## Seed follow-up (filed here)

The seed's checker needs the same nil-into-scalar rule (it enforces the
contract on returns only), so that `f(nil)` into `fn f(v: i64)` is diagnosed
on both engines instead of silently answering true on the seed and false
natively.

## Verification on the next rebuild

Rebuild stage 2 from this source; compile and run both probes with BOTH
backends. Probe 1 (non-optional scalars): every `*_eq` line all `false`,
`*_ne` all `true`, `i64_ifval: some(3) some(4)`, `i64_coalesce: 3 4`, `ret:
false false false false`, `field: false false false true true`, `elem:` all
`false`, `local: false false true true`. Probe 2 (scalar optionals, below)
must print the `exp` column of the optional table, i.e. exactly:

```
param_eq_i64: false false true true false false
param_ne_i64: true false false
param_eq_bool: false false true true false
param_eq_f64: false false true false
param_eq_i32_u8: false true false true
identity: false true false true false true
raw_to_opt: false false 3
ifval: some(3) some(0) none some(3) some(true) some(false) none some(3.0) none
coalesce: 3 0 99 3 true false 3.0 9.5
exists: present present absent
try: false true 103
unwrap: 3 0
match: some(3) some(0) none some(true) some(false) none
local: false false true false false false 3 99 true
reassign: true false 3
field: false false false true true true 3 99
elem: false true false 3 99
dict: false true 3 99
closure: false true
DONE
```

Then re-check the HIR cache: `SIMPLE_HIR_CODEC_ROUNDTRIP=1` must print
`HIRROUNDTRIP ok=true stable=true` and a second identical build must report
`[hir-cache] hits == modules`.

Probe 1 is the program in the first version of this record (kept in git
history at `7725bd9efb5`); probe 2:

```simple
struct Holder:
    oi: i64?
    ob: bool?
    of: f64?

fn id_i64(v: i64?) -> i64?:
    v
fn id_bool(v: bool?) -> bool?:
    v
fn id_f64(v: f64?) -> f64?:
    v
fn mk_i64(v: i64) -> i64?:
    Some(v)
fn mk_bool(v: bool) -> bool?:
    Some(v)
fn mk_f64(v: f64) -> f64?:
    Some(v)
fn none_i64() -> i64?:
    nil
fn none_bool() -> bool?:
    nil
fn raw_to_opt(v: i64) -> i64?:
    v
fn eq_nil_i64(v: i64?) -> bool:
    v == nil
fn ne_nil_i64(v: i64?) -> bool:
    v != nil
fn eq_nil_bool(v: bool?) -> bool:
    v == nil
fn eq_nil_f64(v: f64?) -> bool:
    v == nil
fn eq_nil_i32(v: i32?) -> bool:
    v == nil
fn eq_nil_u8(v: u8?) -> bool:
    v == nil
fn ifval_i64(v: i64?) -> text:
    if val x = v:
        "some({x})"
    else:
        "none"
fn ifval_bool(v: bool?) -> text:
    if val x = v:
        "some({x})"
    else:
        "none"
fn ifval_f64(v: f64?) -> text:
    if val x = v:
        "some({x})"
    else:
        "none"
fn coalesce_i64(v: i64?) -> i64:
    v ?? 99
fn coalesce_bool(v: bool?) -> bool:
    v ?? false
fn coalesce_f64(v: f64?) -> f64:
    v ?? 9.5
fn exists_i64(v: i64?) -> text:
    if v.?:
        "present"
    else:
        "absent"
fn try_i64(v: i64?) -> i64?:
    val x = v?
    x + 100
fn unwrap_i64(v: i64?) -> i64:
    v.unwrap()
fn match_i64(v: i64?) -> text:
    match v:
        case Some(x): "some({x})"
        case nil: "none"
fn match_bool(v: bool?) -> text:
    match v:
        case Some(x): "some({x})"
        case nil: "none"

fn main():
    print "param_eq_i64: {eq_nil_i64(mk_i64(3))} {eq_nil_i64(mk_i64(0))} {eq_nil_i64(none_i64())} {eq_nil_i64(nil)} {eq_nil_i64(3)} {eq_nil_i64(Some(3))}"
    print "param_ne_i64: {ne_nil_i64(mk_i64(3))} {ne_nil_i64(none_i64())} {ne_nil_i64(nil)}"
    print "param_eq_bool: {eq_nil_bool(mk_bool(true))} {eq_nil_bool(mk_bool(false))} {eq_nil_bool(none_bool())} {eq_nil_bool(nil)} {eq_nil_bool(true)}"
    print "param_eq_f64: {eq_nil_f64(mk_f64(3.0))} {eq_nil_f64(mk_f64(0.0))} {eq_nil_f64(nil)} {eq_nil_f64(1.5)}"
    print "param_eq_i32_u8: {eq_nil_i32(3)} {eq_nil_i32(nil)} {eq_nil_u8(3)} {eq_nil_u8(nil)}"
    print "identity: {eq_nil_i64(id_i64(mk_i64(3)))} {eq_nil_i64(id_i64(nil))} {eq_nil_bool(id_bool(mk_bool(true)))} {eq_nil_bool(id_bool(nil))} {eq_nil_f64(id_f64(mk_f64(3.0)))} {eq_nil_f64(id_f64(nil))}"
    print "raw_to_opt: {eq_nil_i64(raw_to_opt(3))} {eq_nil_i64(raw_to_opt(0))} {coalesce_i64(raw_to_opt(3))}"
    print "ifval: {ifval_i64(mk_i64(3))} {ifval_i64(mk_i64(0))} {ifval_i64(nil)} {ifval_i64(3)} {ifval_bool(mk_bool(true))} {ifval_bool(mk_bool(false))} {ifval_bool(nil)} {ifval_f64(mk_f64(3.0))} {ifval_f64(nil)}"
    print "coalesce: {coalesce_i64(mk_i64(3))} {coalesce_i64(mk_i64(0))} {coalesce_i64(nil)} {coalesce_i64(3)} {coalesce_bool(mk_bool(true))} {coalesce_bool(nil)} {coalesce_f64(mk_f64(3.0))} {coalesce_f64(nil)}"
    print "exists: {exists_i64(mk_i64(3))} {exists_i64(mk_i64(0))} {exists_i64(nil)}"
    print "try: {try_i64(mk_i64(3)) == nil} {try_i64(nil) == nil} {try_i64(mk_i64(3)) ?? -1}"
    print "unwrap: {unwrap_i64(mk_i64(3))} {unwrap_i64(mk_i64(0))}"
    print "match: {match_i64(mk_i64(3))} {match_i64(mk_i64(0))} {match_i64(nil)} {match_bool(mk_bool(true))} {match_bool(mk_bool(false))} {match_bool(nil)}"
    val l3: i64? = 3
    val l0: i64? = 0
    val ln: i64? = nil
    val lb: bool? = true
    val lbf: bool? = false
    val lf: f64? = 3.0
    print "local: {l3 == nil} {l0 == nil} {ln == nil} {lb == nil} {lbf == nil} {lf == nil} {l3 ?? 99} {ln ?? 99} {lb ?? false}"
    var m: i64? = 3
    m = nil
    val was_nil = m == nil
    m = 3
    print "reassign: {was_nil} {m == nil} {m ?? 99}"
    val h = Holder(oi: 3, ob: true, of: 3.0)
    val hn = Holder(oi: nil, ob: nil, of: nil)
    print "field: {h.oi == nil} {h.ob == nil} {h.of == nil} {hn.oi == nil} {hn.ob == nil} {hn.of == nil} {h.oi ?? 99} {hn.oi ?? 99}"
    val arr: [i64?] = [3, nil, 0]
    print "elem: {arr[0] == nil} {arr[1] == nil} {arr[2] == nil} {arr[0] ?? 99} {arr[1] ?? 99}"
    val d: Dict<text, i64?> = {"a": 3, "n": nil}
    print "dict: {d["a"] == nil} {d["n"] == nil} {d["a"] ?? 99} {d["n"] ?? 99}"
    val cap: i64? = 3
    val capn: i64? = nil
    val f1 = \: cap == nil
    val f2 = \: capn == nil
    print "closure: {f1()} {f2()}"
    print "DONE"
```

(`while val x = cur:` was dropped from the probe: the seed interpreter itself
loops forever on it with `cur = nil` inside the body, so it has no oracle.)

Build recipe (Windows, frozen stage 2): `simple.exe native-build --target
x86_64-pc-windows-msvc --backend <llvm|cranelift> --runtime-bundle
core-c-bootstrap --runtime-path <stage2-runtime-authority> --entry-closure
--entry <probe inside the checkout's src/> --mode one-binary --output probe.exe`
with `SIMPLE_SCV_INVENTORY_COLD_INIT=1 SIMPLE_WINDOWS_ABI=msvc
SIMPLE_LINKER_FLAVOR=msvc CC=clang-cl.exe` and `tools/` present in the checkout.

## Still open (follow-ups, not in this series)

- Cranelift: annotated `val ov: i64? = 3` reads as nil (Tuple([Bool,T]) vs
  i64-handle mismatch lead); re-measure after rebuild.
- LLVM width class: Eq/Ne with i8/i16/i32 left vs i64 right still truncates
  the right operand; Lt/Le/Gt/Ge always use the left width; compares `sext`
  narrow ints even when unsigned.
- Checker: Assign and struct-literal field flows of nil into a scalar slot;
  the seed's own checker rule.

## Related

- `native_i64opt_some0_collapses_to_nil_2026-07-14.md` (why nil is 3, not 0)
- `native_tagged_nil_prints_as_integer_3_in_i64_sink_2026-08-18.md`
- `pure_simple_option_i64_ifval_always_some_eqnil_always_false_2026-08-08.md`
- `option_none_promoted_to_some_by_static_nil_provenance_2026-09-14.md`
- `hir_codec_put_i64_three_encoded_as_nil_native_2026-10-10.md` (sibling branch)
- `optional_nil_arm_stale_producer_2026-10-10.md` (PR #2844, `src/lib/common/
  binary_io.spl` -- explicit `None` arms for an older retained producer; no
  overlap with this series)
