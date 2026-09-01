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
