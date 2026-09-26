# Stage 2 admission arm 2: `starts_with`/`ends_with` with a literal argument return false in candidate-compiled code

- **Filed:** 2026-09-26
- **Status:** FIXED in the pure-Simple MIR lowering
  (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, the
  `starts_with` and `ends_with` rules); Stage 2 lane result recorded at the end.
- **Area:** pure-Simple MIR text-predicate lowering vs. pure-Simple cranelift
  backend Str-constant representation
- **Host:** yoon-note, x86_64-unknown-linux-gnu
- **Reached after:** `seed_cranelift_bare_return_in_inferred_any_fn_traps_2026-09-26.md`
  and `seed_cross_module_selfless_method_drops_receiver_2026-09-26.md` (the
  first two blockers of the day). With both seed fixes carried through a
  rebuilt seed, `frontend_smoke_status=0` (the SIGSEGV is gone) and the probe
  advances to the receiver/route gate, which this defect fails.

## Symptom

`sh scripts/bootstrap/run-phase1-local.shs --jobs=4`:

```
  Stage 2: proving struct receiver/runtime capability
error: Stage 2 struct receiver/runtime capability failed
    | error: stage2 positional Stage-3 route returned unexpected output: src.app.cli.bootstrap_main.spl
VERDICT — ABORTED: stage=stage2 exit=1 signal=none reason=stage2
```

`bootstrap_stage2_struct_receiver=PASS` precedes it: the receiver guard is
fine; the POSITIONAL route (`check-bootstrap-stage2-struct-receiver.shs`,
fixture `scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl`)
prints `src.app.cli.bootstrap_main.spl` where `app.cli.bootstrap_main` is
expected — `module_logical_name_from_path` neither stripped `src/` nor `.spl`.

## Isolation

A 12-line probe compiled through the rejected candidate's positional route
(`--mode dynload --runtime-path <stage2-runtime-authority>`):

```
rel=src/app/cli/x.spl   sw=F   ew=F   sub4=app/cli/x.spl   sub0=src/app/cli/x
```

`substring`/`len` are right; `starts_with("src/")` and `ends_with(".spl")`
are false. The same probe through the seed's Rust pipeline is right.

`objdump -dr` on the candidate-emitted object shows the call shape:

```
rt_interp_cstr(recv) -> rt_strlen -> rt_string_new            ; receiver: ensure_tagged_str, correct
rt_string_new_literal(&"src/", 4) -> rt_strlen(TAGGED) -> rt_string_new(TAGGED, n)   ; prefix: double-tagged
rt_string_starts_with(recv, garbage_prefix)                   ; -> 0
```

## Root cause

`method_calls_literals.spl` `starts_with`/`ends_with` rules tagged the
argument with an unconditional `rt_strlen` + `rt_string_new`, assuming a Str
constant lowers to a raw `char*` (true for the seed's Rust backend). The
pure-Simple cranelift adapter (`70.backend/backend/cranelift_codegen_adapter.spl`
`case Str(v)`) emits every Str constant as `rt_string_new_literal(ptr, len)`,
i.e. already tagged. Re-tagging a tagged value copies `RtCoreString` header
bytes as the prefix, so `memcmp` never matches. The receiver had been moved to
the runtime-checked `ensure_tagged_str` (rt_interp_cstr unwrap, then tag) in
2026-07; the argument had not. `contains` already routed its needle through
`ensure_tagged_str` and was unaffected.

## Fix

Both rules now pass the argument through `self.ensure_tagged_str(...)`, the
same idempotent tagging the receiver and `contains` use. Backend-agnostic: a
raw literal is tagged once, a tagged literal is unwrapped and re-tagged once.

## Specs

- `test/01_unit/compiler/backend/text_predicate_literal_arg_native_spec.spl`
  — reproducing: literal prefix/suffix on a `val` receiver, positional route,
  exact transcript `sw=T ew=T sw2=F ew2=F`.
- `test/01_unit/compiler/backend/text_predicate_argument_shapes_native_spec.spl`
  — generalization: literal receiver, variable prefix/suffix, concat-result
  receiver, `contains`, empty prefix.

Both honour `SIMPLE_BINARY` (compiler) and `SIMPLE_RUNTIME_PATH` (runtime
capsule, selects `--mode dynload --runtime-path`). The defect is in the
candidate's own pipeline, so they only reproduce against a stage candidate;
the deployed seed emits raw literals and passes them either way.

## Stage 2 lane result

See the end of this record for the phase-1 verdict after the fix.
