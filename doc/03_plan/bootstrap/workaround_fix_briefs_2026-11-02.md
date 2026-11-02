# Workaround real-fix briefs (2026-11-02)

Base: `origin/release/1.0.0`. Source of truth for sites: `git grep -n '@workaround bug=<id>' -- src`.
Inventory: `doc/03_plan/bootstrap/workaround_inventory_2026-11-01.md`. Phase-3 link-level list (read only):
`C:/dev/p3new/linkdry/WORKAROUNDS.md`.

Rules for every lane: failing spec first (red), pure-Simple fix, green, high-effort diff review (zero P0/P1), land via PR.
Do NOT remove `@workaround` tags (the revert loop does that after the stage3 self-build). Code must parse on the
frozen stage2 (no `expr else: x` on continuation lines, no new syntax). `nil`/`Any` only inside `unsafe:`.
"Current source only" = the fix lives in `src/compiler` and benefits the stage3 self-build once a stage3 binary
compiles the tree without the tags. Where a "stage2-safe form" is needed, it is stated per brief.
Out of scope (owned elsewhere): WA-AR-1 (llvm-ar rsp), object cache key, codegen memory, dynload sharding, first-.o
latency, native_codegen_pool.

Lane order (impact = sites x phase-3 relevance): B1 poll_payload, B2 methods-mir, B3 ownerlayout, then B4 ctor-mir,
B5 generic-class methods + facade mangling.

---

## B1. stage2_poll_payload_typeparam_match_2026-11-01 (11 sites, P1, blocks phase 3)
- Open bug: payload binder of `case Poll.Ready(x)` on `Poll<Result<A,E>>` is typed `T` (type param not substituted
  with the subject's type argument), so a nested `match x: case Ok/Err` is ambiguous when a second enum declares Ok/Err.
- Repro idea: bug file `doc/08_tracking/bug/stage2_poll_payload_typeparam_match_2026-11-01.md` has a 12-line repro
  (`Poll<Result<[u8], text>>` + a second enum with `Ok`/`Err`). Use the in-process seed HIR+MIR spec pattern of
  `test/01_unit/compiler/50.mir/enum_owner_unqualified_arms_spec.spl`; assert no `ambiguous` / `has type T` diagnostic.
  Existing `test/01_unit/lib/nogc_async_mut/io/async_buffer_poll_payload_wa_spec.spl` covers only the workaround.
- Owner: `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (enum-match payload binder typing; bare-variant
  resolution ~L4182-4292), `src/compiler/20.hir/return_type_interface_v1.spl`.
- Approach: when binding a payload of generic enum `E<T..>` from a subject typed `E<A..>`, substitute T:=A for the
  binder type so the nested match subject resolves to `Result<A,E>`. If subject args are unknown keep today's path.
- Scope: current source only. Sites in `src/lib/nogc_async_mut/io/buffer.spl` stay tagged.
- Lane B1 owns the substitution helper; B4 builds on it.

## B2. methods-mir-20261031 (30 tagged sites; related mir_unresolved_method_inferred_receiver_2026-10-24, 75 sites)
- Open bug (shapes 1-3 reproduce on current source): (1) untyped param used with `value[a:b]` / `.substring`
  (`.len()` now lowers); (2) call result of an fn without declared return type then `.len()`; (3) `text?` local after
  `if x == nil: return` (no flow narrowing in MIR). Shapes 4-6 are full-closure only: the lane must NOT claim them.
- Repro/spec: `test/01_unit/compiler/50.mir/methods_mir_receiver_shapes_spec.spl` (PR #5771) already records shapes 1-3 as the
  red baseline; make them pass.
- Owner: `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, `method_calls_literals.spl` (receiver type
  resolution); `src/compiler/30.types` for inferred return types of unannotated fns (shape 2).
- Approach: shape 2 - MIR reads the inferred return type from the 30.types result when no declared type; shape 3 - narrow
  `T?` to `T` after an early-return nil guard in the receiver-type lookup (flow-local table); shape 1 - receiver typing
  from call-site instantiation, or a clear type error (stay fail-closed; never a const-0 placeholder).
- Scope: current source only. Sites: `src/lib/common/serialization/__init__.spl` (14), `src/lib/nogc_sync_mut/io/process_ops.spl` (9),
  `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl` (3), `src/lib/common/sdn/parser.spl`,
  `src/compiler/30.types/type_infer/typed_module_owner_v1.spl`.

## B3. ownerlayout-mir-20261031 (12 tagged sites; ~67 `struct_value_syms[...] =` writers)
- Open bug: field read `e.message` on an `unwrap_err()` result is "ambiguous struct/class owner 'CompileError'" when two
  `struct CompileError` exist (`src/compiler/10.frontend/core/backend_types.spl:429`, `src/compiler/70.backend/backend/backend_types.spl:402`).
  Root bug 2 (`SymbolId.name`) is already fixed.
- Repro/spec: `test/01_unit/compiler/50.mir/compile_error_owner_layout_spec.spl` (PR #5774); the unwrap_err shape fails.
- Owner: MIR owner provenance - `resolve_field_index`, `resolve_base_struct_name`, `struct_value_syms` writers
  (`src/compiler/50.mir/_MirLowering*`).
- Approach: register value provenance with the module-qualified `composite_layout_key` of the HIR-resolved symbol (call
  result / Result payload type) instead of the bare name. Add one writer helper, migrate writers incrementally, keep the
  bare-name tier as fallback (no collateral regressions; report time + RSS).
- Scope: current source only. driver_bootstrap.spl, backend_lean, backend_vhdl helpers stay tagged.

## B4. ctor-mir-20261031 (15 sites; items 1b, 2, 3, 4 open; item 1a fixed)
- Open bugs: (1b) `match ring.take(1)` on `Ring<i64,i64>` gives E-RTI-003 unsubstituted `result(opt(p0), RErr)`;
  (2) `case Ok(nil)` on that subject gives "nil sub-pattern requires a declared optional payload slot" (follows from 1b);
  (3) `[Fut<text>]` field gives "array return record element has conflicting or unknown provider field types"
  (`result_err_field_type_key` returns "" for a field typed `Poll<T>`); (4) bare variants of an unimported enum give
  "missing runtime identity for CompileResult" / bare-name collision.
- Repro/spec: `test/01_unit/compiler/50.mir/generic_self_method_result_ctor_spec.spl` (PR #5781): open shapes are
  `skip(..)` with exact diagnostics; flip them to `it`.
- Owner: `switch_operators_calls.spl` (`rti_enum_match_subject_type` ~L2768, array-element owner check ~L1281-1327),
  `result_err_record_owner.spl:26`, `src/compiler/20.hir/return_type_interface_v1.spl` (`receiver_owner` ~L745 drops type args).
- Approach (design note in the bug file): `receiver_owner` returns `Named(_, args)`; instantiate the method row with owner
  args then method args; key generic record fields by instantiated type; take payload enum identity from the callee's
  declared return type.
- Scope: current source only. Starts after B1 lands (same substitution helper). Order: 1b+2, then 3, then 4.

## B5. generic-class methods not lowered (WA-BC-1/2) + facade-path method mangling (SdnBackendImpl)
- Open bug (per `C:/dev/p3new/linkdry/WORKAROUNDS.md`): frozen stage2 MIR skips `is_generic_template` methods; mono only
  specializes direct calls, so self-calls inside a specialization and static `SimpleRing<i64,i64>.create` keep unmangled
  names with no body (undefined `SimpleRing.{create,_advance,...}`, `Future.poll`). Step 0 is to CHECK current source: PR #5732
  (generics-erased-body) emits erased generic bodies; `doc/08_tracking/bug/erased_generic_body_mir_transient_scope_ice_2026_11_01.md`
  is its open P1 follow-up. Write a red spec first (a generic class with a self-calling method used via a concrete
  instantiation must emit a defined body for every referenced symbol); if it is green on current source, record
  "revert-ready after stage3" and stop.
- Facade mangling: `src/compiler/80.driver/driver.spl:37` imports `SdnBackendImpl` via the facade path `compiler.backend.sdn`,
  while the type is defined in `src/compiler/70.backend/backend/sdn.spl`; the impl method symbol
  (`SdnBackendImpl.process_module`) is mangled under the importing path and does not match the definer's symbol, which
  leaves it undefined at link (see `stage2_native_build_run_fn_undefined_reference_link_failure_2026-08-08.md` and
  `bootstrap_default_len_is_empty_not_materialized_2026-07-13.md` defsym aliases). Spec: symbol-name-level check that the
  callee symbol at a facade-imported call site equals the definer's exported symbol. Related:
  `mir_facade_mirlowering_silent_unresolved_import_2026-09-01.md`. The lane-A draft doc was not found on
  `origin/release/1.0.0`; derive from the above.
- Scope: current source. Stage2-safe form only if a source edit is chosen (importing from the defining module), which is a
  workaround, not the fix.

## Not assigned a fix lane (no red spec possible)
- enumowner-mir-20261031 (25 sites) and inferarm-mir-20261031 (20 sites): not reproducible outside the full stage3 closure
  (specs from PR #5772/#5773 are green in the reduced closure). Status: revert-ready pending a full-closure stage3 build
  without the annotations (phase-3 owner). B1 may remove enumowner symptom 1.
- Already revert-ready per the inventory: rti007-mir, rti007_any_return_rows, rti004-mono, mono-call-inference, lambdaabi-mir,
  typeparam-mir (static factories), stage2_module_global_assign_no_binding.
