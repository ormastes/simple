# Qualified-import call statement (`module.func()`) lowers to an empty function body

**Status:** fixed — `bbe045e92ce` (2026-07-29), re-verified at HEAD 2026-08-01

## RESOLUTION (2026-08-01 re-verification)

**Two separate things were reported here as one bug. One was never a bug; the
other was real and is already fixed.**

1. **`body.stmts.len() == 0` was NOT a drop — it is the normal tail-value
   desugar and was a red herring.** For a *value-returning* body
   (`fn main() -> i64:`), `lower_hir_block`
   (`src/compiler/20.hir/hir_lowering/expressions.spl:1787-1817`) lifts the
   trailing expression-statement out of `stmts` into `HirBlock.has` / `.value`.
   A sole-statement body therefore *always* has `stmts.len() == 0`, qualified
   call or not (an ordinary `fn f() -> i64: g()` behaves identically). The
   original probe printed only `stmts.len()` and never read `body.has` /
   `body.value`, so it could not distinguish "lifted to tail value" from
   "dropped". `lowering.errors.len() == 0` was correct, not a silent failure.

2. **The real defect was in the `ExprKind.MethodCall` lowering arm.**
   `provider.answer()` parses as `MethodCall(receiver, method, args)`, but the
   module-namespace redirect existed only in the sibling `Field` arm. The call
   therefore lowered to `HirExprKind.MethodCall` on a `Module` symbol — which
   has no runtime receiver and no such class method — so it survived
   structurally but was semantically dead, with no diagnostic. Fixed in
   `bbe045e92ce` by mirroring the Field arm's intent
   (`expressions.spl:513-568`); a contributing landmine (`SymbolKind` enum
   patterns never matching cross-module, `rt_enum_discriminant == -1`) is filed
   separately as
   `doc/08_tracking/bug/symbolkind_enum_match_fails_cross_module_discriminant_minus_one_2026-07-29.md`.

**Regression guard:** `test/01_unit/compiler/hir/qualified_import_call_spec.spl`
(added by the same commit; single file, no stale duplicate basename). Its third
example is an *unqualified* control that pins the tail-value shape, so a future
reader cannot re-derive misreading #1.

### Re-verification evidence (2026-08-01, seed oracle `src/compiler_rust/target/bootstrap/simple`)

Command (both directions):
`src/compiler_rust/target/bootstrap/simple test test/01_unit/compiler/hir/qualified_import_call_spec.spl`

| Tree state | Result |
|---|---|
| HEAD as-is (fix present) | **3 examples, 0 failures** |
| Fix disabled (one-line mutation at `expressions.spl:549`, gating the MethodCall module-redirect off) | **3 examples, 2 failures** |

The two failures are exactly the qualified-call examples; the third example —
the *unqualified* control — still passes in both directions. So the guard is
**non-vacuous** (it goes red when the fix is removed) and **specific** (it does
not simply fail wholesale). The mutation was reverted and `expressions.spl`
restored byte-identical (sha256 `ed9bcafb34a6…`).

This doc was left at `Status: open` only because the fix commit never touched
it.

## Original report (2026-07-29) — kept verbatim below; see RESOLUTION above

**Found:** 2026-07-29 (lane RIS1, `resolve_import_symbols_spec.spl` repair)
**Area:** HIR lowering (`src/compiler/20.hir/hir_lowering/`), statement/call
lowering for the `import MODULE` qualified-access form
**Severity as reported:** medium-high — "the call is silently discarded rather
than erroring, so downstream passes (MIR, codegen) see a function with no body
at all". Corrected: the call was never discarded, it was lowered to a
semantically dead `MethodCall` on a module namespace (see RESOLUTION #2).

## Finding

A function whose **only statement** is a module-qualified call
(`provider.answer()`, reached via `import provider`, not `use provider.*` /
`use provider.{answer}`) lowers with **zero statements** in its HIR body,
instead of one `Expr(Call(...))` statement.

Minimal repro (isolated probe, not the target spec — no name collision with
the imported symbol needed):

```simple
val src_provider = "pub fn answer() -> i64:\n    42"
val provider = parse_full_frontend(src_provider, "provider", "provider", log)
val src_consumer = "import provider\nfn main() -> i64:\n    provider.answer()"
val consumer = parse_full_frontend(src_consumer, "consumer_qualified2", "consumer_qualified2", log)

var modules: Dict<text, Module> = {}
modules["provider"] = provider
var sources: [SourceFile] = []
sources = sources.push(SourceFile(path: "provider", content: src_provider, module_name: "provider"))
val surfaces = module_surfaces_from_modules(modules, sources).unwrap()  # Ok

var lowering = hirlowering_for_module("consumer_qualified2", surfaces)
val hir = lowering.lower_module(consumer)

print "errors={lowering.errors.len()}"      # 0 -- no diagnostic at all
for fn_ in hir.functions.values():
    print "fn {fn_.name} stmts_len={fn_.body.stmts.len()}"
    # -> "fn main stmts_len=0"   <-- BUG: source has exactly one statement
```

Also reproduced with a name collision (local `fn answer()` alongside
`import provider` and a call to `provider.answer()`) — same result, both
`answer` and `main` lower with `stmts_len=0`.

`lowering.errors.len()` is **0** — this is a silent drop, not a diagnosed
failure. Downstream, `resolve_import_symbols_spec.spl`'s "resolves a
module-qualified imported function call" example indexes
`fn_.body.stmts[0]` expecting the call statement and gets:

```
semantic: array index out of bounds: index is 0 but length is 0
```

## Scope not fully bisected

Not confirmed whether this is specific to:
- the qualified-access expression form (`MODULE.func()`) as a bare statement
  vs. as part of a larger expression, or
- statements reached only through the `import MODULE` qualified-import
  declaration specifically (as opposed to `use MODULE.*` — a call through a
  glob import, e.g. `inner_fn()` after `use pkg.inner.*`, was separately
  confirmed to lower and execute correctly in this same spec's "glob import
  follows a facade's named re-exports" example, which passes).

Re-investigation should start at the call/statement lowering path for
`import`-declared modules in `src/compiler/20.hir/hir_lowering/` (statement
lowering, not the import pre-registration pass — `lowering.errors.len()`
being 0 suggests the statement is dropped after successful resolution, not
rejected during resolution).

## Impact on this lane

(Historical — resolved.) `resolve_import_symbols_spec.spl`'s "resolves a
module-qualified imported function call" example was left red (not weakened)
pending this fix; `bbe045e92ce` also repaired that example to read
`body.value` when `stmts` is empty. Its
harness plumbing (module_surfaces wiring) is otherwise correct — see
`doc/08_tracking/bug/resolve_import_symbols_spec_field_and_wiring_repair_2026-07-29.md`.

## Related

- `doc/08_tracking/bug/jit_struct_field_compound_assign_loads_zero_2026-07-27.md`
  — different bug, same flavor (silent zero/empty result on the default
  execution path with no diagnostic raised)
