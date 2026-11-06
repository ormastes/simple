# Native stage-3: every same-module instance method call fails "unresolved method call ... struct_method_syms=yes"

- **Status:** fix-implemented-verification-pending (PR work/mirp2-recv). P2.
- **Found:** native W4 sanity on s3_fable44 (`w4_dictfield.spl`, `r.put(...)` on a class `me` method); reproduced on s3_fable46.
- **Layer:** 50.mir `_MirLoweringExpr/method_calls_literals.spl`, `case Unresolved:` instance-method recovery.

## Repro (s3_fable46, native-build --entry-closure, llvm, x86_64-pc-windows-gnu)
`test/04_smoke/recv/recv_w4_dictfield.spl`, `recv_fn_args.spl`, `recv_nested.spl`:
```
unresolved method call: put route=runtime-fallback key=<mod>.Reg::put owner=<mod>.Reg
struct_method_syms=yes record_instance_method=n/a lookup_method_in_type=no
```
Same for `fn` methods (`Bag.has`, `Box.bump`): not `me`-specific, not dict-field-specific.
Also emitted: `[simple-runtime][error] rejected invalid array handle before dereference`.
The seed-interpreted compiler lowers all shapes cleanly (spec below: 7/7) -> stage-3 self-miscompile.

## Root cause
The key IS present (`struct_method_key_present_v1` -> yes) and the next statement is
`resolved_instance_method_raw = self.struct_method_syms[key].id` -- a struct-valued
Dict bracket-read plus field read in one expression, the open native Dict gap
(`dict_native_pitfalls.md`: class-field `d[k]` bracket read). The id came back invalid,
so the call fell through to the runtime-fallback rejection.

## Fix
Bind the `SymbolId` to a typed local first (same shape as the working InstanceMethod
arm `selected_func_id = self.struct_method_syms[key]`), then read `.id`.

## Verification pending
Needs a stage-3 rebuilt from this source; then rerun the three recv_* fixtures
(expect `PASS recv_*`). Related: native_codegen_drops_receiver_for_fn_instance_methods_2026-07-25
(fn-method receiver ABI) can only be re-verified once these calls lower at all.

## Specs
- Repro/prevention (frontend->HIR->MIR, seed-interpreted): `test/01_unit/compiler/50.mir/mir_receiver_shapes_spec.spl`
  (class me+dict field, fn with args, self-call, field-of-field, param receiver, struct fn/me).
- Native fixtures: `test/04_smoke/recv/recv_{w4_dictfield,fn_args,nested}.spl`.
