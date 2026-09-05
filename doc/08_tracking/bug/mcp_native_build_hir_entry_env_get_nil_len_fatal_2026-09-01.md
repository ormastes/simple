# MCP native-build HIR-entry fatal: `.len()` on Option::None from ambiguous `env_get` dispatch

**Date:** 2026-09-01 · **Status:** FIXED (`628ac26d38d`) · **Severity:** blocker (made MCP native build unmeasurable)

## History of the symptom (three layers, one repro command)

Repro: `SIMPLE_EXECUTION_MODE=interpret SIMPLE_NATIVE_BUILD_WORKER=1 <seed> run src/app/cli/native_build_worker.spl src/app/mcp/main.spl`

1. **`undefined field 'symbols' ... on value of type 'bool'`** — previously reported at HIR entry. **Does NOT reproduce** at HEAD `591aad1791e` with a seed freshly rebuilt from that source (md5 `f9bf124d933a0de0af5d999444234996`). Working tree had 47 dirty paths, none under `src/compiler` semantics/driver. The earlier "still present at committed HEAD with a fresh seed" account was measured against a **stale** seed (see 2).
2. **`unknown decorator @always_inline on function file_read_nullable`** — emitted by the *deployed* seed (md5 `c8f08d98969d6288afe2971cc4d5f21f`), which predated whitelist commit `8e643137ca0` (`decorator_apply.rs::is_directive_decorator`). HEAD source already whitelists it; fix = rebuild seed. **Trap:** the mandated `cmp simple.exe deps/simple.exe` FRESH check passed while BOTH copies were stale relative to source — it proves the copies match each other, not that either matches HEAD.
3. **`semantic: method 'len' not found on type 'enum' (receiver value: Option::None)`** — the real remaining fatal, after phase `load_sources` completes. Located via `SIMPLE_INTERP_OOB_DEBUG=1` (+ `SIMPLE_DEBUG_FIELD_ACCESS=1` for the .spl stack):
   `main -> cli_native_build -> compiler_driver_run_compile -> compile -> parse_all_committing_impl -> parse_all_impl -> log_debug -> debug -> _ensure_initialized`

## Root cause (layer 3)

`src/lib/nogc_sync_mut/log.spl:_ensure_initialized` called `env_get(...).len()`.
The `env_get` name has **5 co-compiled definitions with 2 differing signatures**
(`(text)->text` in `std.nogc_sync_mut.env.variables` / `io_runtime` vs
`(text)->Optional(text)` in `std.sffi.system`) — exactly the
`compiler_cross_module_private_symbol_collision` warning the run prints. Under
the full compiler closure, ambiguous dispatch returned `Option::None` for an
unset variable; `.len()` on it is fatal. In isolation (small closure) the
correct overload dispatches and the same code works — which is why unit-level
probes never caught it.

`SIMPLE_RESOLVE_METHODS`: the fatal fires during `parse_all_impl` (phase 1),
before `run_resolve_methods_quiet_gated` (which runs only after phase 3), so
the flag — off (default) or on — cannot influence it. Reproduced with it OFF.

## Fix

`628ac26d38d` — local nil-guarded `_env_text(key)` helper in `log.spl`; the
three `_ensure_initialized` reads route through it. Pure Simple, no platform
behavior, Unix-safe. The broader dispatch ambiguity (5 defs, 2 signatures)
remains open and is the generalizable defect class.

## Specs (both green, 9 examples / 0 failures, commit `e759c76de79`)

- `test/01_unit/lib/log_env_nil_guard_spec.spl` — reproduces the exact contract (unset log env vars; `env_get(...).len()`; `log_debug` path completes).
- `test/01_unit/lib/env_status_provider_len_spec.spl` — generalization: member access on the absent case across the env provider family (text/optional/bool contracts).

## After the fix

The build proceeds past the fatal into `surface_build` (43/100 modules at the
10-minute mark of the first post-fix run); MIR error count measurement in
progress at time of writing — see the lane report.

---

## REOPENED 2026-09-01 (layer 1 DOES still reproduce) — measured

**Provenance:** HEAD `9fb0d279739ab69b6577e875fb645aabae2ab03d`; working tree dirty
(18,861 tracked-diff paths overall, dominated by `doc/` + symlink-as-dir entries;
**25** under `src/` + `scripts/`); seed
`src/compiler_rust/target/release/simple.exe` == `deps/simple.exe`, md5
`286f66b8615dce0e0da788f0550c4008`, 39,120,896 bytes, built 2026-09-01 18:21.
Seed staleness is **discharged for this defect**: the only `.rs` file newer than
the seed is `compiler/src/linker/object_parser.rs` (COFF linker, unrelated), and
`_Items/` has **zero** `.spl` churn since `591aad1791e`. `SIMPLE_RESOLVE_METHODS`
unset (default OFF).

**Result (two independent ~21-minute runs, both rc=1):**
```
step 1/6 parse          100/100 OK (76 s)
step 1/6 surface_build  100/100 OK (~19 min)
step 2/6 hir              0/100 -> FATAL
error: semantic: undefined field 'symbols': cannot access field on value of type 'bool'
```
The section above says layer 1 "does NOT reproduce". That was measured on a
different seed (`f9bf124d933a…`) at `591aad1791e`; the `.spl` sources involved
are byte-identical between the two points, so the difference is either the seed
or run-to-run nondeterminism in the ambiguous-dispatch fallback the run's own
`compiler_cross_module_private_symbol_collision` warnings describe
(`env_get`: 6 defs / 2 signatures; `dir_list`, `file_read_text`, `shell`, …).
Layer 3 (`log.spl` `.len()` on `Option::None`) is genuinely gone — the run gets
~19 minutes further than before `628ac26d38d`.

## Call site pinned with `SIMPLE_DEBUG_FIELD_ACCESS=1`

```
[field-access-error] field=symbols recv_type=bool recv=false expr=Identifier("self")
stack=register_glob_imported_symbols_depth -> register_imported_symbol
 -> register_imported_symbol_inner -> materialize_imported_callable_type_dependencies
 -> materialize_imported_callable_type_dependencies_inner
 -> materialize_imported_callable_dependency
 -> materialize_imported_callable_declared_dependency
 -> materialize_imported_callable_declared_dependency_inner
 -> register_imported_symbol -> register_imported_symbol_inner
 -> register_imported_symbol -> register_imported_symbol_inner
```
`self` itself is the bad receiver: inside a `me` method it evaluates to the
boolean `false`. Owner: `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl`,
`impl HirLowering: me register_imported_symbol_inner` (declared line 183).

Strongest candidate line: **219**, `val terminal_type = self.symbols.lookup_qualified_type_raw(...)`
in the `routed_origin` branch — the statement immediately after the recursive
`self.register_imported_symbol(...)` at 211-214, and the ONLY `self.symbols` in
this method that is the FIRST `self` access after a recursive call.
The sibling site at 516 (legacy re-export chase) is **excluded**: it reads
`self.module_surfaces` before `self.symbols`, so a clobber there would report
`field=module_surfaces`.
Working hypothesis: receiver write-back of a void/mutating `me` call stores a
bool into `self` — the "staged aggregate-receiver accessor hazard" already named
at `80.driver/driver_hir_pipeline_lowering.spl:587`. NOT yet reproduced in a
20-line fixture (a plain class with the same shape does not clobber); the
`impl <Class>:` cross-module extension form is the untested variable.

## Adjacent defect noticed (not proven to be this bug)
`module_import_registration.spl:177` declares `fn surface_name_position(...)`
(a non-`me` function) whose body reads `self.name_index_positions`, and it is
called six times per registration as `self.surface_name_position(...)`.
It happens to work on the seed interpreter, but `fn` + `self` is the same
class-surface divergence recorded in `context_helpers.spl:14-27`.

## MIR error count: STILL NOT OBTAINABLE
MIR lowering is step 3+/6. The build dies at step 2/6 module 0. No MIR error
count can be produced until this is fixed; the last real number remains 133.

### Probe run 1 (2026-09-01) — line 219 REFUTED
Two `eprint` probes were inserted in `register_imported_symbol_inner`
(before line 219 `terminal_type`, tag B; before line 240 `existing_id`, tag C)
and the full build re-run. Result: **B fired 0 times** — the `routed_origin`
branch never executes in this closure, so line 219 is NOT the site and the
"first `self` access after a recursive call" argument does not apply.
**C fired 33 times**, the last with `local=DapSession`, immediately followed by
the `[field-access-error]`. So the failing `self.symbols` is at or after the
composite branch's line 240 within the SAME registration — candidates 243/244
(`self.symbols.symbols.has(...)` / `[...]`), 272-279, or one of the
enum/trait/alias/callable/const branches. A follow-up run with a probe before
every `self.symbols` inside the method is pinning it.

Minimal-fixture status: NOT reproducible small. Three shapes were tried against
the same seed and all behaved correctly — void mutating `me` ending in a dict
assignment, mutual recursion through a `_inner` helper, a mutating bool-returning
`me` called in an `if`, and the same across a cross-module `impl Box:` extension.
Like the layer-3 `env_get` defect, this only manifests under the full compiler
closure, which is consistent with the ambiguous-dispatch warnings the run emits.
