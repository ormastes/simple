# OPEN: native-build dies after `aop_weave` — a 1-argument call binds to `log.spl`'s 2-argument `(scope, msg)` helper

- **Status:** FIXED (triage 2026-11-11, lane boot21; first triaged 2026-11-10 lane boot5) — ambiguous co-compiled duplicate call is a compile error since `10e216d19f8c` (ancestor of HEAD `d552f63f67f8`); the pin spec's execution path repaired in this lane (11 `pub` visibility markers in `eval_tables.spl`) and re-verified 5/5 on the tracked seed (see 2026-11-11 addendum below).
- **Found while** fixing
  `native_build_noop_invocation_frames_raw_i64_mcdc_mode_2026-09-13.md`; this is
  the NEXT blocker uncovered once that one is removed, not the same defect.

## Reproducer

At `origin/main` + the `mcdc_mode` fix, with the two known earlier blockers
worked around:

```
SIMPLE_PACKAGE_INDEX_COLD_INIT=1 SIMPLE_SCV_FREEZE_FALLBACK=1 \
  <seed> native-build --mode=dynload hello.spl
```

where `hello.spl` is:

```
fn main():
    println("hello")
```

The build proceeds through `load_sources`, `mir`, and `aop_weave` (all
`state=complete`), then:

```
error: semantic: function expects argument for parameter 'msg', but none was provided
```

## What is established

`SIMPLE_DEBUG_ARG_BINDING=1` names the binding exactly:

```
[DEBUG arg_binding TMP] missing param 'msg'; full param list=["scope", "msg"]; args given=1
```

`["scope", "msg"]` is the signature of the logging helpers in `src/lib/log.spl`
(`fatal`/`error`/`warn`/`info`/`debug`/`verbose` at lines 720-739; the same
shape repeats in `src/lib/nogc_sync_mut/log.spl:266`). So a call site passing a
**single** argument is resolving to a **two**-argument logger.

This is consistent with the `compiler_cross_module_private_symbol_collision`
class that the same build already reports in bulk — the run emits dozens of
warnings of the form "public function `X` has N co-compiled definitions with
differing signatures ... falling back to the last definition when types are
ambiguous — a fallback hit may still dispatch to the wrong one", naming
`error`-adjacent generic names among others. A one-argument `error("...")` or
`warn("...")` in the weave/backend path colliding with `log.error(scope, msg)`
would produce exactly this.

## What is NOT established

- The specific call site was not located. The diagnostic carries no source
  location, and unlike the `method not found` class there is no
  `SIMPLE_INTERP_OOB_DEBUG` equivalent that prints the `.spl` frame chain for an
  arity mismatch. **Adding one would be worth more than fixing this instance** —
  see the localization notes in the sibling record.
- Whether the offending call is in `aop_weave` itself or in the phase
  immediately after it (the failure prints after `aop_weave state=complete`).
- Whether this is a genuine collision or a plain one-argument call to a
  two-argument function that was never exercised.

## Why it matters

Together with
`stage3_step_omits_package_index_cold_init_scv_authority_missing_2026-09-13.md`,
this is what still stands between the tree and a `native-build` of a three-line
hello world. Until both are closed, no "hello native-builds" gate can be added
as a green row to any harness default sample.

## 2026-11-10 P3-boot5 triage (row 36) — SUPERSEDED

The failure mechanism this record hypothesized — a 1-argument call silently
binding to `log.spl`'s 2-argument `(scope, msg)` helper via the flat
last-write-wins pick among co-compiled definitions with differing signatures —
is closed by `10e216d19f8c` ("fix(resolve): ambiguous co-compiled duplicate
definition is a compile error (owner decision 6)", ancestor of HEAD
`4343ce254922`). The interpreter and seed HIR/MIR now refuse the ambiguous
pick instead of falling back to the last definition; a genuine collision on
`error`/`warn` would be a compile error, not a silent wrong-arity bind, and
the tree clash that motivated it (`std.crypto.sha1` function-local
`bytes_to_hex`) was hoisted to a module-level import in the same commit.
seed-smoke (worktree seed bin/simple.exe, 2026-11-10):
`test/01_unit/compiler/interpreter/ambiguous_co_compiled_fn_call_error_spec.spl`
--mode=interpret -> PASS (5 passed). The "add a `.spl` frame chain for arity
mismatch" tooling wish remains unaddressed but is an enhancement, not this
defect.


## 2026-11-11 P3-boot21 triage — FIXED (header flip)

Fresh re-verification and repair, at HEAD `d552f63f67f8` (first triaged
2026-11-10 lane boot5; header not flipped then):

- `git merge-base --is-ancestor 10e216d19f8c HEAD`: ANCESTOR — ambiguous
  co-compiled duplicate definition is a compile error (owner decision 6), so
  the silent wrong-arity bind this record filed cannot occur at tip.
- The pin spec
  `test/01_unit/compiler/interpreter/ambiguous_co_compiled_fn_call_error_spec.spl`
  (added by `10e216d19f8c`) could not EXECUTE on the tracked seed: the seed's
  visibility enforcement rejects the spec's `use
  compiler.core.interpreter.eval_tables.{...}` imports because all 11 imported
  helpers were private (same drift class as `f865d6154718`, which pubbed a
  batch of helpers for its own specs). Repaired in this lane:
  `src/compiler/10.frontend/core/interpreter/eval_tables.spl` — `pub` added to
  the 11 names the pin spec imports (`func_table_reset`, `func_table_register`,
  `func_table_lookup`, `func_table_register_owned`, `func_import_binding_reset`,
  `func_import_binding_register`, `func_resolve_for_caller`,
  `func_flat_lookup_for_caller`, `func_owners_of`, `func_ambiguous_call_message`,
  `pub val FUNC_LOOKUP_AMBIGUOUS`), plus `func_table_lookup_owned` pubbed while
  unblocking the sibling spec below.
- Seed-smoke after the repair (tracked seed 46fe8f6b6def,
  `--mode=interpreter --no-cache`): SPEC FILE VERDICT outcome=OK, executed=5
  passed=5 failed=0. The five examples pin the exact mechanism: flat table
  still holds the last-registered definition (the hazard), a caller with no
  owned definition and no import route gets `FUNC_LOOKUP_AMBIGUOUS` (=-2) not
  the flat pick, a selective import resolves, single-owner names still resolve,
  and the diagnostic names symbol/owners/caller.

Note: the sibling spec `cross_module_owned_fn_resolution_spec.spl` still
ERRORs on further private-helper drift (`func_import_binding_lookup`,
`struct_table_reset`, `func_import_binding_route`,
`func_module_namespace_lookup`, `func_resolve_module_member_for_caller`, and
`module_loader_core` names) — out of this row's scope, not baselined, left for
the test-repair lane. The ".spl frame chain for arity mismatch" tooling wish
remains an enhancement, not this defect.
