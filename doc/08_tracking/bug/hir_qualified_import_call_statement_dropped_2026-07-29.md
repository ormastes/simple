# Qualified-import call statement (`module.func()`) lowers to an empty function body

**Status:** open
**Found:** 2026-07-29 (lane RIS1, `resolve_import_symbols_spec.spl` repair)
**Area:** HIR lowering (`src/compiler/20.hir/hir_lowering/`), statement/call
lowering for the `import MODULE` qualified-access form
**Severity:** medium-high — the call is silently discarded rather than
erroring, so downstream passes (MIR, codegen) see a function with no body at
all

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

`resolve_import_symbols_spec.spl`'s "resolves a module-qualified imported
function call" example is left red (not weakened) pending this fix. Its
harness plumbing (module_surfaces wiring) is otherwise correct — see
`doc/08_tracking/bug/resolve_import_symbols_spec_field_and_wiring_repair_2026-07-29.md`.

## Related

- `doc/08_tracking/bug/jit_struct_field_compound_assign_loads_zero_2026-07-27.md`
  — different bug, same flavor (silent zero/empty result on the default
  execution path with no diagnostic raised)
