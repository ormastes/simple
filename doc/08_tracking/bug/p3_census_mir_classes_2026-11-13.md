# Phase-3 census (run-19 Stage 2): MIR failure classes (2026-11-13)

Census: `native-build src/app/cli/bootstrap_main.spl` (entry closure, 1619
modules, cranelift, go-to-end, 2 MIR workers) with the run-19 Stage 2 compiler
(`bootstrap-fable-19/.../stage2-admitted/simple`, pinned source `3197fdaa5ed6`)
over the `8cbab25851e` snapshot. HIR 1619/1619; MIR 1618 ok, 3 modules fatal.
Log: `simple-census-20261113/build/p3-census.log`. Fix lane: branch
`work/census-mir-fixes-20261113` (base `dc14e46a737`).

Discriminator used for every class (not a native build, <1.3 GiB, seconds):

    SIMPLE_LIB=<worktree>/src <stage2-admitted>/simple compile <probe>.spl --format=smf -o /tmp/x.smf

`compile` runs the same MIR lowering as the census; the LLVM `llc` step that
follows it fails on this host ("Metadata id is already used") for whole-module
closures and is unrelated (the census is cranelift). Verdict = presence of
`[mir-module-failure]` / `[first-compile-error] MIR lowering error`.

## Class 1 — `is_none` on a `text.to_i64()` result (persisted_graph.spl:96)

`unresolved method call: is_none ... owner= struct_method_syms=no` at
`priority.is_none() or memory.is_none()`, where `priority = fields[3].to_i64()`.

Root cause: `text.to_i64()` is the LENIENT raw-`i64` parse everywhere below
the interpreter — MIR records its result as `Int(64)` on purpose
(`50.mir/_MirLoweringExpr/method_calls_literals.spl` text-special arm:
"`"3".to_i64() ?? d` must not test raw 3 as the nil sentinel"), the C runtime
returns 0 on failure (`rt_string_to_int_lenient` -> `rt_string_to_int`), and
the seed HIR types it `I64`. Only the seed INTERPRETER returns nil on failure
(`interpreter_helpers/method_dispatch.rs:199`). So `.is_none()` on it has no
owner; the compiler is right to refuse. The site was written by `c1e50059d2c`
(safe-code `== nil` -> `.is_none()` sweep) and the `== nil` it replaced was
already vacuous natively. The strict `Option<i64>` parse that all three legs
agree on is `parse_i64()` (`rt_string_parse_int` returns nil on failure; MIR
records `Optional(Int)`; interpreter `string.rs:410`).

Fix: source — `fields[3].parse_i64()` / `fields[5].parse_i64()`.
Spec: `test/01_unit/compiler/action_graph/persisted_graph_decode_row_spec.spl`.
Probe: `to_i64().is_none()` red (same error text), `parse_i64().is_none()` green;
whole `persisted_graph.spl` closure (66 modules) MIR-clean after the fix.

**Recorded, not fixed (language-level):** `text.to_i64()` returns nil on failure
in the interpreter and 0 natively. The idiom `x.to_i64() ?? d` (795 sites under
`src/`) therefore cannot see a failure natively (per the text-special arm's own
comment, "`"3".to_i64() ?? d` must not test raw 3 as the nil sentinel"; the
`??` lowering itself was not traced here), and `x.to_i64() == nil` compares a
raw integer with the nil word. A `.is_none()` on a non-Optional receiver should be a HIR type
error; today it surfaces only as this MIR fatal. Owner decision needed: make
`to_i64` a real `i64?` (runtime + MIR representation change) or lint the
`?? d` / `== nil` / `.is_none()` forms on its result toward `parse_i64()`.

## Class 3 — `HirStmtKind.Let` payload 1 typed `HirType?` (statements.spl, 3 sites)

`enum construction 'HirStmtKind.Let': payload type mismatch at 1` at the three
`HirStmtKind.Let(symbol, binding_type, init)` constructions
(census snapshot lines 1067 / 1191 / 1231; tip 1106 / 1230 / 1270).

Shape: `val hir_type = if has_annotation: self.lower_type(t) else: nil` then
`val binding_type: HirType = if has_annotation: hir_type else: payload(..)`.
`hir_type` is a nullable merge; the join for `binding_type` is `HirType?`, and
HIR records THAT for the annotated symbol — `SIMPLE_ENUM_PAYLOAD_TRACE=1` on the
probe: `expected='named#0' remembered='named#0?' source='named#0?'`. MIR then
refuses a `T?` word in a non-optional payload slot (never widen nil). Probes:
bare-arm join red (also red with `hir_type: HT?` + `None`); `val x: HT =
lower(..)` green; `if val annotated = hir_type: annotated else: ..` green.

Fix: source — the three joins unwrap through `if val annotated_type = hir_type:`.
Behaviour is identical when `lower_type` yields a value; a nil from `lower_type`
under an annotation now falls to `binding_payload_type` instead of constructing
a Let with a nil type word.
Spec: `test/01_unit/compiler/mir/annotated_let_from_optional_arm_spec.spl`.

**Recorded, not fixed (HIR):** an annotated `val x: T = <if-join of T? and T>`
is typed `T?` by HIR — the annotation is dropped silently and the nullable
widening is neither reported by HIR nor by the HIR census; only the MIR payload
check catches it, and only when `x` flows into an enum payload. The pre-existing
`else: nil` arms in safe code at statements.spl:1082/1204/1239 remain
`never-widen-nil` debt (the Let `type_` slot is a plain nullable by design,
see the comment block above line 1043).

## Class 4 — `MirConstValue.Str(i64)` (synthetic_driver_codegen.spl:77-78)

`enum construction 'MirConstValue.Str': payload type mismatch at 0` at
`manifest_fields["driver_class"] = MirConstValue.Str(manifest.driver_class)`
and `...Str(manifest.vendor)`. `DriverManifestAttr.driver_class` and `.vendor`
are `i64` (`00.common/_Attributes/decl_attrs.spl:137-138`); the payload check
is correct. The constant is consumed only as an opaque `MirConstValue.Struct`
(`mir_instruction_graph.spl` renders it `zeroinitializer`), so no consumer
expected text.

Fix: source — `MirConstValue.Int(..)` for both. Probe red with `Str(i64)`;
whole `synthetic_driver_codegen.spl` closure (143 modules) MIR-clean after.
Spec: `test/01_unit/compiler/mir/synthetic_driver_manifest_const_payload_spec.spl`.

## Class 2 — bare struct names re-registered with different field lists

`[mir-lower] WARNING: struct/class name 'X' re-registered with a DIFFERENT
field list (...; keeping EXISTING)` for `JoinPoint` ([kind, kind_function_name,
kind_signature, kind_location, kind_error_type, block_id, instruction_index,
context] vs [kind, source_symbol, target_symbol, logical_join_point_id]),
`TextSpan` ([start, end] vs [value, start, len]) and `ElfSymbol`
([st_name, st_info, st_other, st_shndx, st_value, st_size, name] vs
[name, sym_bind, sym_type, section_index, value, size]). These are the only
three names in the whole census log.

State at both the pinned source and the tip: the registry already has a
module-qualified tier (`composite_layout_key` / `declared_struct_layout_key`,
`module_lowering.spl:838-920`), the bare tier is first-wins, the conflicting
bare name is recorded in `struct_field_order_conflict_warned`, and the main
read paths fail closed on it (`struct_value_layout_key`, `resolve_field_index`
`function_lowering.spl:2143-2300`). So the warning is a canary, not itself a
miscompile.

Audit of all 103 reads of the `struct_field_*` dictionaries under 50.mir
(89 `[..]` + 14 `.get(`): 9 qualified, 27 guarded, 47 registration-side,
**20 UNGUARDED bare-name reads**, reached two ways:
(A) `struct_value_syms` holds a bare name (writers `switch_operators_calls:1603`,
`expr_dispatch:1394/2110/2111/3504`, bare fallback of
`struct_value_provenance_key`); readers `mir_lowering_stmts:716-719`
(field count sets the aggregate copy size), `:1093-1095`, `:1142/1152/1157/1169`
(array-move copy skipping), `expr_dispatch:2017/2061-2064` (struct equality
loop), `provider_metadata:1382-1383` (method-receiver typing).
(B) `struct_field_type_name` stores the BARE nested field type name
(`module_lowering:1790`); the recursive struct copy (`mir_lowering_stmts:772`)
and equality (`expr_dispatch:2080/2112`) follow it with `.contains` only, so a
correctly qualified outer struct with a `TextSpan`/`JoinPoint`/`ElfSymbol`
field still copies/compares the nested value with the FIRST-registered layout.
Also `module_lowering:4338/4357` (prescan, bare) and bare writes outside the
conflict detector (`module_lowering:3333/3493`, `declaration_inventory_barriers_v1:53`,
`bootstrap_type_registration:62/137/162/181`).
Conditionally unguarded: `lower_struct_construct` (`switch_operators_calls:6620-6771`)
when the callee symbol is unresolved (`:9166` passes the bare `direct_name`).

Decision (this lane): fix the two recursion ROOTS, not the 20 reads.
`copy_struct_value_recursive` (`mir_lowering_stmts.spl`) and
`lower_struct_structural_eq` (`expr_dispatch.spl`) (a) fail closed with
`error_fatal` when their layout key is a bare name in
`struct_field_order_conflict_warned`, and (b) recurse into a nested record
through the module-qualified layout recorded per field in
`struct_field_type_ownership_key` (= `composite_layout_key` of the field type,
`module_lowering.spl:1790`) folded by `declared_struct_layout_key`, keeping the
bare name only for the symbol lookup. Both re-entry claims of the audit were
verified by reading the recursion sites (`:772`, `:2112`). Blast radius: only
names in `conflict_warned` fire -- three in this census -- so the next census
may trade a silent copy/compare of `JoinPoint`/`TextSpan`/`ElfSymbol` reached
through bare provenance for a loud per-module fatal naming the layout.
Spec: `test/01_unit/compiler/mir/same_named_struct_layouts_across_modules_spec.spl`
(+ `test/fixtures/compiler/same_name_layouts/span_{a,b}.spl`), interpreter-green,
UNEXECUTED natively: a 50.mir change cannot be executed in this lane (the census
compiler carries its own MIR; no Stage 2 rebuild). Load/parse evidence: a
MIR-loading seed spec (`array_projected_receiver_types_spec.spl`) runs 6/7 with
and without the change (the 1 failure is pre-existing on the base).

Remaining unguarded sites, NOT fixed here (named gaps): `mir_lowering_stmts:1093-1095`
(array move ctor count), `:1142/1152/1157/1169` (array-move copy skipping),
`provider_metadata:1382-1383` (method-receiver typing), `module_lowering:4338/4357`
(prescan), `switch_operators_calls:9166` (bare `direct_name` for an unresolved
callee), and the bare writers outside the conflict detector listed above.

## Class 5 — Unknown call origin aborts BOTH codegen workers (`callee=env_get`)

After MIR 1619/1619, native_compile reached 31/808 and both MIR shard workers
died with SIGABRT right after `MIR call target lacks proven source/runtime/
foreign origin: callee=env_get` (log ~26519/26521): every remaining codegen
unit was lost (`failed_modules=1619`). Same fail-stop shape as the two OPEN
records `unknown_call_origin_panics_codegen_worker_2026-11-12.md` and
`unknown_call_origin_driver_hir_archive_stage3_2026-11-13.md`; the #8815 ICE
boundary (`driver_ice_boundary.spl`) only ATTRIBUTES a panic to a module, it
cannot continue past it.

(b) Fixed here (fail closed, per module): `mir_unproven_call_origin_sites_v1`
(`50.mir/mir_instruction_graph.spl`) names every `Const(Str, FuncPtr)` operand
with `call_origin == Unknown` in `Call.func`, `Call.args`, `PipeForward.func`,
`Parallel.funcs`; `_compile_selected_module` (`driver_aot_native_output.spl`)
returns `_aot_compile_failure(name, "unproven-call-origin: ...")` before any
backend runs, so the module is recorded failed in the ICE boundary's CAUGHT
tier and staged codegen continues. The detail keeps the panic's own stem so
existing greps still match. Unknown is never mapped to Source; other
FuncPtr-value positions keep the backend panic as a backstop.
Spec: `test/01_unit/compiler/mir/unproven_call_origin_module_census_spec.spl`
(seed-executed, 3/3).

(a) Producer NOT identified in this lane. `provider_callable_call_origin_v1`
(`provider_metadata.spl:214-227`) answers Unknown when the callee symbol is
absent from the table, is not a Function/Method, or has no
`callable_text_value_abi` row under `{defining_module}::{name}`. `env_get` has
FOUR definitions (`lib/nogc_sync_mut/io_runtime.spl:426`,
`lib/nogc_sync_mut/env/variables.spl:28`, `lib/nogc_sync_mut/io/env_ops.spl:52`
re-exported as `std.io.env_get`, `lib/gc_async_mut/env/variables.spl:8`).
Stage 2 `compile --format=smf` probes of `use std.nogc_sync_mut.io.env_ops.{env_get}`
and `use std.io.{env_get}` both reached codegen without the panic, so the
single-module `compile` path does not reproduce the entry-closure registration;
the only closure module importing `env_get` among the first-listed crashed
units is `src/app/cli/bootstrap_focused_native_build.spl:11`
(`use std.nogc_sync_mut.io.env_ops.{env_get, env_set}`). With (b) landed the
next census names the module and function directly.

## Borrow class — `short borrow escapes` on `&mut local` into an extern out-slot

Stage borrow, 3 sites (coordinator listed 2; the log has 3):
`compiler.backend.linker.lld_sffi:43:1` (`lld_elf_link`:
`spl_dlsym_process_checked("simple_lld_elf_link", &mut fptr)`),
`lib.nogc_sync_mut.sffi.dynamic:92:1` (`_sffi_i64_out_transport_honoured`:
`spl_wffi_try_call_i64_out(0, [], 0, &mut probe)`) and `:105:1`
(`_sffi_call_i64_checked`, same extern, `&mut value`). All three externs take
`*mut i64` and are called inside `unsafe(capabilities: [ffi, raw_ptr])`.

Mechanism: `_param_effect` (`35.semantics/param_effects/infer.spl:575-577`)
gives EVERY extern pointer/class parameter the effect `foreign-unknown`; the
borrow checker routes Foreign/Unknown callees through
`record_short_call_contract` (`55.borrow/borrow_check/mod.spl:690`) and
`check_short_call` (`nll_short_calls.spl:182`) records the escape for any
argument whose place carries a loan under a mode that is not
`read-short`/`mutate-short`. There is NO way today for an `extern fn` to declare
a non-retaining out-slot contract: `FunctionAttr` has no such field, and adding
one means a HirFunction field plus a HIR codec wire-format bump (see
`c79be829a86`). Not changed in this lane; nothing on `release/1.0.0` since the
pinned source touches this (`git log 3197fda..HEAD -- 35.semantics/param_effects
55.borrow` = import repairs only). Owner decision: (1) an extern parameter
contract attribute (e.g. declare the `*mut i64` out slot `mutate-short`), or
(2) rewrite the three sites to pass a raw address obtained in `unsafe` instead
of `&mut local`. Not acceptable: weakening `check_short_call`.


### Fix (option 2 / review option B) — out slot passed by address

The two externs now take the out slot as an `i64` ADDRESS
(`src/lib/nogc_sync_mut/sffi/dynamic.spl:37` `spl_dlsym_process_checked(name,
out_symbol: i64)`, `:51` `spl_wffi_try_call_i64_out(..., out_value: i64)`); the
C ABI (`int64_t*`, `runtime_dynload.c:2099`, `runtime_native.c:11490/11617`) is
unchanged. The three callers allocate a caller-owned 8-byte heap cell with the
in-tree idiom (`ffi/llvm_types.spl:86-94`): `rt_alloc(8)` → `rt_ptr_write_i64(slot,
0, 0)` → call → `rt_ptr_read_i64(slot, 0)` → `rt_free(slot)`, with no return
between alloc and free (lld_sffi.spl `lld_elf_link`; dynamic.spl
`_sffi_i64_out_transport_honoured`, `_sffi_call_i64_checked`). An `i64` carries
no loan, so `check_short_call` has nothing to escape; the checker is untouched.
`_sffi_i64_out_transport_honoured` is KEPT (re-purposed to the address form, not
vacuous): natively the C provider answers `SPL_WFFI_NULL_FUNCTION` (2) → true;
the seed interpreter (`interpreter_extern/wsffi.rs:747`) recognises only a
`Value::BorrowMut` out and answers 1 → false, which is exactly the switch that
keeps `_sffi_call_i64_checked` on the `[status, value]` fallback transport there.
The comment at the old dynamic.spl:144 already recorded that the Cranelift lane
passed `&mut handle` as the slot VALUE — the address form also removes that.

Evidence (census stage2 `compile --format=smf`, bootstrap-fable-19, same
compiler as the census):
- shape probes, census-identical message: `red.spl` (`&mut value`) →
  `[first-compile-error] 5:1: short borrow escapes: call argument requires a
  checked non-retaining short contract`, rc=1; `green.spl` (address) → rc=0,
  `.smf` emitted; same red→green for the lld shape (`lld_red.spl` 2 hits /
  `lld_green.spl` 0).
- module level: `compile src/compiler/70.backend/linker/lld_sffi.spl` (its
  closure includes `sffi/dynamic.spl`) at the pre-fix source reports exactly the
  three census sites (`lld_sffi:43:1`, `dynamic:92:1`, `dynamic:105:1`), rc=1;
  post-fix: 0 `short borrow` lines, borrow stage passed, pipeline ran on to the
  host llc step (fails with the known unrelated "Metadata id is already used"
  on whole closures; census is cranelift). `compile
  src/lib/nogc_sync_mut/sffi/dynamic.spl` alone SIGSEGVs (rc=139, not the
  MemoryMax) in HIR at `lib.common.crypto.types` reexport-chase before borrow —
  a separate pre-existing stage2 finding, not addressed here.
- seed spec `test/01_unit/compiler/borrow/extern_out_slot_address_form_spec.spl`
  6/6: both census shapes red (`check_mir_module` reports the contract escape)
  and both address forms green, plus the null-function probe by address
  (status ∈ {1, 2}, slot reads back 0) and a real-value round-trip through the
  public `DynLib.call_checked("labs", [-7])` → `Ok(7)` (mutation to `Ok(8)` fails
  5/6). `sffi_admission_spec` 11/11,
  `dynamic_loader_spec` 11/11 unchanged. The native out-slot writeback itself is
  UNEXECUTED by a seed run: the seed answers status 1 without writing, so on the
  seed `_sffi_call_i64_checked` now ALWAYS takes the `[status, value]` fallback
  (a consequence of option B, not a defect; the labs round-trip above runs
  through that fallback).
- cost (accepted price of option B): one 8-byte `rt_alloc`/`rt_free` per checked
  call natively, two pairs + the fallback call on the seed. `DynI64FnSlot` is the
  cached hot path; upgrade path if a measurement ever shows it matters: a
  per-slot owned out cell allocated once in `resolve`. Not built.
- `check-no-direct-rt.shs --roots src`: both files are allowlisted
  (`scripts/check/no_direct_rt_allowlist.txt:9` covers `src/lib/nogc_sync_mut/sffi/`,
  `:57` covers `suffix:_sffi.spl`); measured forbidden count is 6760 at base and tip
  (delta 0). The ratchet is already red on `origin/release/1.0.0` (6760 vs baseline
  6290, pre-existing); baseline not touched here.

Residuals (not changed here):
- seed `interpreter_extern/wsffi.rs:439` `spl_dlsym_process_checked` raises
  `CompileError::runtime("output must be &mut i64")` for an address out; its
  only caller `lld_elf_link` is reached only under `is_simpleos_target()`
  (`native_linking.spl:592`), so a seed-interpreted SimpleOS link would now
  error instead of returning exit_code 127. Accepting `Value::Int(addr)` there
  is a seed change (rebuild) — owner decision.
- seed std copy `src/compiler_rust/lib/std/src/plugin/__init__.spl:24/41` still
  declares the `*mut i64` form (seed-only stdlib, not read by stage2).

### Follow-up ratchet — other `&mut local` into extern out-slots (NOT fixed here)

Same shape, not flagged by this census (the borrow stage flags per module and
these modules were not among the 5 `[go-to-end] failed`; why `dynamic.spl:149/176`
in the SAME module passed while 92/105 failed is not understood — record it, do
not assume they are safe). Review lead: `check_short_call` (`55.borrow/borrow_check/nll_short_calls.spl:166-183`) fires only when the argument conflicts with a loan alias live in `state`; both unflagged sites have an `if … return Err` guard between the `var` and the call while both flagged sites are straight-line — likely loan-state loss across a join (a checker gap, not a safety proof). Single-line `*mut i64` extern decls (non-exhaustive;
multi-line decls such as `spl_wffi_call_i64_into_bytes` `out_len`, the
`rt_torch_*_checked` family, `rt_value_as_string`, `rt_file_stat` appear only in
the site list below): `spl_dlopen_checked`,
`spl_dlsym_checked` (`dynamic.spl:31/35`, `plugin_startup.spl:35/37`,
`wsffi/mod.spl:17/21`). Reproducible census (23 sites, 2026-11-13):

    grep -rn "&mut [a-z_]*)" src --include=*.spl | grep -v vendor | grep -E \
      "spl_dlopen_checked|spl_dlsym_checked|spl_dlsym_process_checked|spl_wffi_try_call_i64_out|spl_wffi_call_i64_into_bytes|rt_[a-z_0-9]*\("

`wsffi/mod.spl:35/44`, `plugin_startup.spl:310/323/325`, `sffi/dynamic.spl:149/176`,
`sffi/spl_fonts.spl:81/322`, `gpu/engine2d/backend_metal.spl:86/97`,
`torch/sffi.spl:297-353` (8 `rt_torch_*_checked`), `ffi_gen.specs/runtime_value_full.spl:606`,
seed std `plugin/__init__.spl:89/113`, `packaging_build.spl:221`. Suggested ratchet:
freeze this list in a `scripts/check/` baseline and fail on growth; convert sites
to the address idiom as they are touched.
## Census state at hand-off

MIR phase complete 1619/1619 (progress counter said `failed=1`; the
`[go-to-end] failed` lines name 5 modules: the 3 MIR classes above + 2 borrow
modules). Codegen: 31/808 then both workers aborted (class 5), exit 1.
