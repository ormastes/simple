# BUG: an imported module-level const has no cross-module HIR linkage

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

**Re-verification (2026-08-10):** Reproduced fresh on
`bin/release/x86_64-unknown-linux-gnu/simple` (seed) via `native-build
--runtime-bundle core-c-bootstrap --mode one-binary --entry-closure`:
- Cross-import case (`use owner.{BASE}` + `print(BASE)`): still fails with
  `MIR lowering error: undefined variable: BASE` — exact match to the
  original symptom.
- Blocking-bug control case (`val BASE: i64 = 5` + `print(BASE)` in the SAME
  module, no import): still fails to build, now with a different error
  (`MIR lowering error: unsupported MIR type kind [infer-arm]:
  HirTypeKind::Infer((0, 0))` instead of the originally-reported "MIR module
  has no functions" message) — the blocking bug
  (`native_build_mir_module_has_no_functions_2026-07-25.md`) is itself
  unresolved, so the doc's own precondition ("verify against a control that
  passes") still cannot be met. Root cause at
  `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` (missing
  `qualify_imported_function_symbol`-equivalent for `Const` imports) is
  unchanged on inspection. Left OPEN and blocked, per the doc's own ordering
  — applying the const-import fix without the `lower_static` bypass and a
  passing control remains an active link-time-duplicate-symbol hazard.
**Found:** 2026-07-25
**Related:** `952d2ca34d7` fixed the SAME-module half of this defect.
**Blocked by:** `doc/08_tracking/bug/native_build_mir_module_has_no_functions_2026-07-25.md`

## Symptom

A module-level global referenced across an import fails to lower, even when it
is a plain scalar `i64`:

```
use owner.{BASE}        -> MIR lowering error: undefined variable: BASE
use owner; owner.BASE   -> HIR lowering error ... unresolved
```

Importing accessor **functions** instead of the global is the workaround.

## Root cause — `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:502-503`

The `Const` import branch defines a symbol and stops:

```
elif as_const != nil:
    self.symbols.define(local_name, SymbolKind.Const, nil, import_span, Visibility.Public, false, Some(imported_mod_name))
```

Compare the `Function` branch immediately above (498-501), which additionally
calls `qualify_imported_function_symbol` to link the use site to the defining
module's mangled symbol. A const gets **no** cross-module linkage.

The importer's `HirModule.constants` is built solely from its own
`module.constants` (same file, ~line 1339). So the imported name exists as a
symbol with no `HirConst` behind it → MIR's `lower_const` never runs for it →
its id never enters `global_symbol_ids` / `global_const_exprs` →
`try_lower_global_read` (`_MirLoweringExpr/expr_dispatch.spl:98-99`) returns nil
→ `undefined variable`.

(Verified: the missing `qualify_*` call at 502-503 and the `_skip_dirs`
exclusion below were both confirmed by direct inspection.)

## Why the natural fix was NOT shipped — concrete link-time hazard

The obvious fix is to capture the owner's `Const` decl at the import site and
lower it into the importer's constants under the importer's own symbol id. That
was implemented, linted clean, and did not regress a trivial build — then
**reverted**, because the constants loop calls `lower_const` **and**
`lower_static`, and statics are emitted with an **unmangled** global name:

`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:170`
```
val g_name = "@g_{static_.name}"
```

Under `--mode one-binary`, owner and importer would both emit `@g_BASE` — a
duplicate global definition at link time.

**Any fix of this shape must route imported consts to `lower_const` ONLY,
bypassing `lower_static`.** That cannot be validated today, because no module
containing a module-level `val` builds at all (see the blocking bug).

An attempted patch (197 lines) exists as a starting point but is deliberately
not committed; it must not be applied without the `lower_static` bypass and a
control that actually passes.

## Order of work

1. Fix the `MIR module has no functions` regression first — it blocks this, the
   deep-free chain, and the seed native-build gate.
2. Reapply the const-import fix WITH the `lower_static` bypass.
3. Verify against a control that passes (`val BASE: i64 = 5` printed from
   `main` must build and print `5` before any cross-import A/B is meaningful —
   today it does not, so every such A/B is VOID, not negative).
