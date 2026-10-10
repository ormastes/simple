# Native: `v == nil` is true for the integer 3 (both backends) and for bool `true` (LLVM) on non-optional scalars; scalar optionals lose nil through unboxed producers

**Status:** source fixes on `work/rel-native-nil-compare-rebased-20261010`
(the series rebased onto `release/1.0` after PR #2882); they take effect only in a REBUILT stage 2
and are NOT yet verified natively (see "Verification on the next rebuild").
**Engines:** staged-native (stage 2 and later), `--backend llvm` and
`--backend cranelift`; also the seed's default JIT `run` lane. The tree-walk
interpreter (`SIMPLE_EXECUTION_MODE=interpret`) is the oracle.
**Found via:** `HirCodecWriter.put_i64` / `put_bool` writing `N` for 3 / true
so the stage-2 HIR cache never hit
(`hir_codec_put_i64_three_encoded_as_nil_native_2026-10-10.md`; its codec-only
fix landed first as PR #2882, see "Codec mechanism after the rebase").

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
3. Retyped the nil-aware scalar declaration `StateVariant.suspension_point_id`
   to `i64?`.

   **Codec mechanism after the rebase.** The HIR codec writers are NOT
   retyped. `put_i64(v: i64)`, `put_bool(v: bool)`, `hc_i64_key_before_v1(left:
   i64, right: i64)` and `_hc_i64_index_before_v1` keep release's
   rendered-text discriminator (`"{v}" == "nil"`, PR #2882) as their ONE
   mechanism; both codec files are byte-identical to release except
   `hc_read_f64` (audit below). An earlier revision of this series retyped the
   first three to `i64?` / `bool?` with `v == nil`, and the first rebase kept
   that form. Review blocked it, correctly: the typed form assumed "a plain
   scalar argument arrives as `Some(v)`", which holds for FREE-function calls
   only. Method-call arguments are passed raw
   (`method_call_optional_param_arg_not_boxed_2026-10-11.md`), all 1,301
   `put_i64` and 121 `put_bool` sites in `generated/hir_codec.spl` are method
   calls, and `v == nil` on the `i64?` parameter lowers to `rt_is_none(v)`,
   which is true for the raw word 3 -- so `w.put_i64(3)` would have written
   `N` again in any compiler built by this lowering (the #2882 bug). The
   interpreted specs could not see it (`hir_codec_nil_scalar_optional_spec`
   passed 4/4 with the typed form). Interaction of the kept form with this
   series: the writers contain no `== nil` on a scalar, so the fold has
   nothing to fold there (lowering probe: `"{v}" == "nil"` stays a text
   compare); a non-optional parameter is never boxed and the checker rule is a
   diagnostic only, so a nil reaching such a parameter is the raw sentinel
   word exactly as before the series -- it renders `nil` under the interpreter
   and, as the codec record states, is indistinguishable from the integer 3
   natively. The writers must only be given plain scalars: under the
   interpreter a nil `i64?` argument renders `Option::None` and `put_bool(nil)`
   writes `0`; no production caller does either (the generated codec writes a
   presence line, then the unwrapped payload).
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
producers {return, binding, call-arg, field, nil literal, extern/Dict/untyped} x
consumers {`== nil`, `!= nil`, `if val`, `.?`, `unwrap`, `??`, `?`, match}).
Neighbouring specs `null_coalesce_lowering_spec`, `optional_float_nil_compare
_lowering_spec`, `option_return_boxing_paths_spec`, `local_mir_type_nilable_
contract_spec`, `hir_codec_roundtrip_spec` (3/4), `hir_codec_key_order_v1_spec`
(2/6), `hir_codec_writer_audit_v1_spec` (1) are red IDENTICALLY on the
unmodified base (measured by checking out the original files) -- pre-existing.

## W-nil-compare: sites that relied on a typed scalar carrying nil

Direct scalar-typed param/local `== nil` in `src/compiler`: 5 sites, all HIR
codec, all removed by PR #2882 (rendered-text test, fix 3).

**The "38 call sites / 2088 functions" figures first recorded here were
wrong** and are superseded by the audit below: that scan keyed on the callee
NAME only (so `symbols.get(name) == nil` on a Dict counted as "`get -> i32`")
and counted every `-> T?` function with a `nil` line as a scalar one.

### Audit: nil-tests of a `-> <scalar>` call result (pre-landing requirement)

Oracle fact that bounds the problem (seed probes, `SIMPLE_EXECUTION_MODE=
interpret`): the seed REJECTS a nil leaving any non-optional return at
runtime, whatever its origin (`return nil`, a `nil` tail, an untyped value
that happens to be nil): `error: semantic: nil is forbidden by the
non-optional return contract of 'f'`. So under the seed a `-> <scalar>`
function never yields nil and `f() == nil` is never true; only natively did
the word 3 leak through. Retyping to `T?` is what makes such a test mean
something on both engines.

What the fold actually reaches (in-process lowering probe, same harness as
`scalar_nil_compare_folds_to_constant_spec`): FOLDED -- free `-> i64` call
(`== nil`, `??`), a local bound from one, a method on a TYPED user receiver,
a wrapper `-> i64` that returns an extern's result, a non-optional scalar
struct field, `xs[i]` on `[i64]`. NOT folded (runtime test kept) -- a direct
extern call, `a?.m() ?? d`, text builtins (`to_i64`, `index_of`,
`parse_int`), `Dict.get` / `d[k]`, any untyped receiver.

Scan (src/compiler, src/lib, src/app; 14,066 `.spl`, 145,757 definitions
indexed; forms `f() == nil` / `!= nil` (27), `if val x = f()` (55), `f().?`
(24), `f() ?? d` (2,405), and `val x = f()` later nil-tested (784)): 3,295
hits on a callee NAME that has at least one `-> <scalar>` definition. Each
was resolved to the callee definition(s) (same file, `use` import,
`self`/owner, declared receiver type; the rest by hand):

| class | hits | disposition |
|---|---|---|
| callee resolves to a `T?` / `Option` / struct / text return | 941 | not scalar; not folded |
| builtin receiver (text / Dict / array), no user definition | 845 | builtin lowering (`parse_int`/`parse_f64` carry the runtime-value marker) |
| untyped receiver, collection/text method name (`get` 666, `to_i64` 484, `index_of` 149, `find` 53, `first`/`last`/`pop` 11) | 1,363 | builtin; the 15 in a file that names a class with a scalar `get` were read: all Dict |
| untyped receiver, other names (`read_u32`/`read_u16` 35, `as_int`/`as_bool` 23, `get_int` 19, `source_to_addr` 7, ...) | 97 | read one by one: the callee is `T?`/`Option`/`Result`, or the receiver is a dynamic/untyped value that the fold does not reach (`BinaryReader.read_u32 -> u32?`, interpreter `Value.as_int -> Option<i64>`, `DbRow.get_int -> i64?`, `DebugInfoBridge.source_to_addr -> i64?`, `AdaptiveMap.remove -> V?`, ...) |
| direct EXTERN `-> i64` result | 27 | already excluded from the fold (`extern_fn_symbols` -> `extern_result_locals`): `10.frontend/parser_types.spl:449,458`, `parser_types_expr.spl` x17 (83..267, `rt_enum_payload` / `rt_tuple_get`), `70.backend/backend/cranelift_codegen_adapter.spl:762..820` x8 (`rt_tuple_get`) |
| undeclared runtime builtin (`rt_file_read_text` x10 in src/app/check + src/app/deps, `rt_file_write_text` x1 in `nogc_async_mut/mcp/main_lazy_json.spl:307`) | 11 | untyped call, not folded |
| scan false positives (docstring `wm_chrome_theme.spl:351`, shadowed local `95.interp/mir_interpreter.spl:573`, `std.gc` `GcHeap.allocate -> [u8]?`, `match_pattern -> Dict<text, text>?` x2) | 5 | none |
| **user-defined, non-extern `-> <scalar>` callee** | **6** | table below |

So the true number of such call sites is **6, not 38** (2 in `src/compiler`):

| site | test | callee | returns nil? | decision |
|---|---|---|---|---|
| `src/compiler/70.backend/linker/link_deps.spl:56` | `?? false` | `get_config_bool(section, key, default_val) -> bool` (`std.config_parser`) | no; the call omitted `default_val` (seed: arity error) | dead test removed, `false` passed as the default |
| `src/compiler/80.driver/shb/shb_extractor.spl:81` | `?? ""` | `decl_get_ret_type -> i64` | no (-1 or a type tag) | dead test removed |
| `src/lib/nogc_sync_mut/src/config.spl:664` | `?? 4` | `parse_int -> i64` (same file) | no (0 on garbage) | dead test removed |
| `src/app/mcp/startup_log.spl:16`, `src/app/simple_lsp_mcp/startup_log.spl:16` | `?? 0` | `time_now_unix_micros -> i64` (wrapper of extern `rt_time_now_unix_micros`) | no | dead test removed (x2) |
| `src/lib/nogc_async_mut/async_host/worker_thread.spl:79` | `task_id == nil` | `ThreadSafeQueue.try_pop -> usize` (0 = empty) | no | **not changed, reported**: dead on both engines today (0 is not the word 3); the intended test is `== 0`, and the `match task_id: case Some(id)` below treats the `usize` as an Option. Fixing it changes behaviour under the seed; not in the compiler closure |

No callee had to be excluded from the fold beyond the extern results above.

Functions declared `-> <scalar>` that return a nil LITERAL: **3, not 2088**
(none of them has a nil-testing caller in src/):

| function | decision |
|---|---|
| `FlatPoolReader.decode_nullable_i64(raw) -> i64` (`10.frontend/core/flat_pool_codec.spl:260`) | retyped `-> i64?`; callers: `hir_codec_reader_budget_v1_spec` only |
| `FlatPoolReader.decode_nullable_bool(raw) -> bool` (`:276`) | retyped `-> bool?`; same spec (its `decode_nullable_bool("2")` example stopped dying on this contract; it now reaches the next one, `decode_text -> text` returning nil -- text, out of scope here) |
| `hc_read_f64(r) -> f64` (`20.hir/hir_codec_support.spl:477`), `return nil` x2 when the reader is poisoned | `return 0.0`, mirroring `next_i64`'s `return 0`; sole caller is the generated codec, which discards the value once `r.ok` is false. Under the seed a truncated float literal was a hard error instead of a cache miss |

Limits of the audit: text resolution, not the type checker. A `-> <scalar>`
function that returns an untyped / Optional / extern value without a nil
literal is invisible to it (the seed errors on that path, natively the word
leaks), and so is a receiver whose class is only known by inference in a
file that never names it.

Text builtins that are TOTAL under the seed but nil-tested anyway
(`s.to_i64() == nil` / `if val x = s.to_i64()`; the seed returns 0, never
nil): 13 sites, 2 in `src/compiler` (`80.driver/cache/gateway/
semantic_scope_live_owner_v2.spl:670`, `80.driver/cache/publication/
selected_head_reopen_validation.spl:61`), 4 in `nogc_sync_mut/play/wm/
mod.spl`. Dead under the oracle already (the author meant `parse_int`);
unchanged, since switching them changes seed behaviour.

### Audit: the two seed divergences in the tree

**`fn h(v: i64): v == nil` (nil into a scalar parameter / annotated local).**
Functions that nil-test (`==`, `!=`, `??`, `.?`, `if val`) a parameter or an
annotated local of non-optional scalar type: **0** in src/compiler, src/lib
and src/app (two independent scans). Nothing relies on it.

**`B(i: nil).i == nil` (nil stored in a non-optional scalar field).**

- Stores: explicit `field: nil` into a declared scalar field at **15**
  constructor sites over 5 struct types, all `# DESUGARED` `has_x` / `x: T`
  pairs: `ParserField.fixed_address` (`10.frontend/desugar/
  state_enum.spl:170`), `MacroCall.span` / `MacroArg.span` (`35.semantics/
  macro_check/mod.spl:100,274`), `TemplateError.span` (`macro_check/
  template.spl:134`), `TypeInfo.bits` / `.signed` / `.lanes` (`99.loader/
  loader/compiler_sffi.spl:1272..1297`, 11). Fields simply omitted from a
  constructor are not countable by text and add to this.
- Tests: `.field == nil` / `!= nil` / `?? d` / `.?` / `if val` hits on a
  field NAME with a scalar declaration: 628; 332 resolve to an Optional or
  struct field, 4 to a scalar one, 290 have a receiver the scan could not
  type (117 compiler, 78 lib, 95 app). The compiler ones were read: Optional
  or struct (`PackageModuleIndexReadV1.generation`, `CompileOptions.opt_level:
  i64?`, `MachOProviderV1.minimum_os: Option<i64>`, `once: bool?`, ...) except
  the rows below. lib/app (173) were sampled (12 highest-ratio names), not
  read exhaustively: none stored nil (e.g. `Engine2DReadback.backend_handle`
  is always built with 0 although the comment at `simple_web_html_layout_
  renderer_paint_tiles_gpu.spl:234` says nil).
- **No nil-test reads any of the 5 nil-storing fields** (readers gate on
  `has_x`), so nothing in the tree relies on the divergence.

| site | test | field | decision |
|---|---|---|---|
| `src/compiler/70.backend/linker/mold.spl:518-520` | `config.pie ?? true`, `.debug ?? false`, `.verbose ?? false` | `LinkConfig.pie/debug/verbose: bool`, never built with nil | dead tests removed (3) |
| `src/compiler/20.hir/portable_body_graph.spl:151` | `edge.caller_symbol_id == nil or edge.callee_symbol_id == nil` | `PortableBodyDependencyEdgeV1.*_symbol_id: i64` | tests removed (2): subsumed by the membership test at line 139 -- `node_set[node] = true` is only reached for nodes that passed `node == nil or node < 0` (line 137), so `not node_set.has(edge.*_symbol_id)` already rejects a nil id; the `< 0` and membership checks stay |
| `20.hir/hir_lowering/_Items/declaration_lowering.spl:839`, `trait_impl_lowering.spl:56` | `if f.bits.?:` | `BitfieldField.bits: i64` (0 with `has_bits` false) | unchanged: `.?` on a scalar folds to the VALUE, and the seed's `.?` on an int also yields the value (`0.?` -> 0, falsy), so both engines take the same branch |

Known consequence, not fixed and not new: a desugared field that holds nil
and is written by the generated HIR codec (`w.put_i64(node.fixed_address)`)
is the raw word 3 natively, so the native compiler writes `3` where the seed
writes `N` (already stated in the codec record). Readers gate on
`has_fixed_address` and the round trip is stable, but the cache bytes differ
between the two engines for those fields; storing 0 instead of nil at the 15
sites (as `_FlatAstBridge/module_assembly.spl` already does) would remove it.

### Array elements

`xs[7] == nil` on a declared `[i64]` folds to false, while `rt_array_get`
returns the nil word for an out-of-bounds index. The seed does not answer
true there either: it raises `array index out of bounds: index is 7 but
length is 2`. So an out-of-bounds read that used to be observable natively as
"nil" is now indistinguishable from the integer 3; bounds must be checked
with `i < xs.len()`.

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
- Method-call arguments are not coerced to Option handles for `T?`
  parameters (`method_call_optional_param_arg_not_boxed_2026-10-11.md`); the
  representation rule of fix 5 holds for free-function calls only until that
  is fixed. The HIR codec writers stay on the rendered-text form regardless.
- Checker: Assign and struct-literal field flows of nil into a scalar slot;
  the seed's own checker rule.

## Related

- `native_i64opt_some0_collapses_to_nil_2026-07-14.md` (why nil is 3, not 0)
- `native_tagged_nil_prints_as_integer_3_in_i64_sink_2026-08-18.md`
- `pure_simple_option_i64_ifval_always_some_eqnil_always_false_2026-08-08.md`
- `option_none_promoted_to_some_by_static_nil_provenance_2026-09-14.md`
- `hir_codec_put_i64_three_encoded_as_nil_native_2026-10-10.md` (PR #2882; the mechanism the codec keeps)
- `optional_nil_arm_stale_producer_2026-10-10.md` (PR #2844, `src/lib/common/
  binary_io.spl` -- explicit `None` arms for an older retained producer; no
  overlap with this series)
