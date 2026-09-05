# native (bootstrap/entry-closure): module-level `val` globals read as uninitialized stack garbage

- **Date:** 2026-07-23  **Status:** FIXED (three-layer fix, same change set)
- **Severity:** critical — any native app using a module-level `val` (e.g.
  `simple_lsp_mcp_server`'s `SERVER_NAME`) SIGSEGVs or misbehaves at startup.

## Symptom
`val REPRO_NAME = "repro-server"` / `val REPRO_CAP: i64 = 1024*1024` at module
level compile to an **uninitialized `alloca` + `load`** in the emitted LLVM —
text globals read as `2147483652`-style garbage, i64 globals as 0. Interpolating
or passing the text value derefs garbage → `SIGSEGV at address (nil)`.
No compile error is raised (silent).

## Root-cause chain (probe-verified, W68–W76)
1. **HIR** `hir_lowering/_Items/module_lowering.spl` — `lower_module`'s
   bootstrap branch early-returns a `HirModule(... constants: {} ...)`
   **hard-coded empty**, dropping the AST module constants the flat bridge
   correctly assembled (`module_assembly.spl` fills `Module.constants`).
2. **MIR** `_MirLowering/module_lowering.spl` — the bootstrap branch of
   `lower_module` returns before the non-bootstrap constants loop, so even
   present constants were never lowered/registered (`global_symbol_ids`,
   `module.constants`).
3. **MIR expr** `_MirLoweringExpr/expr_dispatch.spl` — a module-global
   reference misses `local_map` in the Var/NamedVar pre-dispatch, falls through
   to the big match, which mis-dispatches NamedVar into UnitLit's bare
   `new_temp` (documented seed match hazard) → undefined local, **no
   diagnostic**, backend emits alloca-without-store.

## Fix (same-named files)
- HIR bootstrap return: lower `module.constants` via `lower_const` and pass
  them in the constructed `HirModule`.
- MIR bootstrap branch + `bootstrap_globals.spl` entry/extra paths: run
  `lower_const` (+`lower_static`) over `hir_module.constants` BEFORE function
  lowering.
- Pre-dispatch: after `local_map` miss, consult `try_lower_global_read`
  (scalar const inline / static LoadGlobal) before falling through.

## Known ceilings (follow-ups, not covered by this fix)
- Cross-module module-`val` references (constants dict is per-module lowering).
- Mutable module `var` in natives (needs static storage emission + init).
- The UnitLit mis-dispatch itself still exists for other unhandled expr kinds —
  any silent fall-through emits an undefined local instead of a diagnostic.

## Repro
`src/app/mcprepro`-style entry with the two `val`s above; native-build with
`--entry-closure`; run and check output (fixed: `name=repro-server cap=1048576`).
