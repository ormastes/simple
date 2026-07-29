# `SymbolTable.get_symbol(SymbolId(id: 0))` returns nil for a validly-registered symbol

**Status:** open
**Found:** 2026-07-29 (lane RIS1, `resolve_import_symbols_spec.spl` repair)
**Area:** HIR symbol table (`src/compiler/20.hir/hir_types.spl`, `get_symbol`
around line 332)
**Severity:** medium — silently drops metadata (e.g. `defining_module`) for
whichever symbol happens to be the first one registered in a table

## Finding

`hir_types.spl`'s `SymbolTable.get_symbol(id: SymbolId?) -> Symbol?`:

```simple
fn get_symbol(id: SymbolId?) -> Symbol?:
    match id:
        case SymbolId(raw):
            val found: Symbol? = self.symbols[raw]
            found
        case _:
            nil
```

returns `nil` when `raw == 0`, even though `SymbolId.is_valid()` explicitly
treats 0 as a valid id (`self.id >= 0`), and even though `lookup("...")` for
that same name returns `SymbolId(id: 0)` successfully (proving the symbol
really is registered at id 0 in `self.symbols`).

Reproduced via the "2-pass import resolver" pre-registration path used by
`resolve_import_symbols_spec.spl`'s "named import from module A wins over
same-named symbol from module B" example: a consumer module explicitly
importing `CompileOptions` from module `a` (the first and only cross-module
symbol registered ahead of ordinary lowering) gets assigned `SymbolId(id: 0)`
by the pre-registration pass. `lookup("CompileOptions")` correctly returns
`SymbolId(id: 0)`, but the immediately following
`get_symbol(SymbolId(id: 0))` returns `nil`, so the example's
`defining_module` assertion sees a `nil` where a `Symbol` was expected:

```
expected nil to be truthy
```

(previously masked by the pre-existing spec bug at
`doc/08_tracking/bug/resolve_import_symbols_spec_field_and_wiring_repair_2026-07-29.md`
— see that doc for the `.? != to_equal(true)` fix that was needed just to
observe this failure honestly instead of a false positive/negative).

## Isolated repro

```simple
val log = Logger(level: 0)
val src_a = "struct CompileOptions:\n    input_files: [text]\n    only_in_a: i64"
val module_a = parse_full_frontend(src_a, "a", "a", log)
val src_b = "struct CompileOptions:\n    mode: text\n    only_in_b: i64"
val module_b = parse_full_frontend(src_b, "b", "b", log)
val module_consumer = parse_full_frontend("use a.{CompileOptions}", "consumer", "consumer", log)

var modules_map: Dict<text, Module> = {}
modules_map["a"] = module_a
modules_map["b"] = module_b
var sources: [SourceFile] = []
sources = sources.push(SourceFile(path: "a", content: src_a, module_name: "a"))
sources = sources.push(SourceFile(path: "b", content: src_b, module_name: "b"))
val surfaces = module_surfaces_from_modules(modules_map, sources).unwrap()  # Ok

var lowering = hirlowering_for_module("consumer", surfaces)
val hir = lowering.lower_module(module_consumer)

val resolved_id = hir.symbols.lookup("CompileOptions")
print "resolved_id present={resolved_id.?}"          # SymbolId(id: 0) -> truthy
val sym = hir.symbols.get_symbol(resolved_id)
print "sym present={sym.?}"                            # nil  <-- BUG: should be the Symbol
```

Verified deterministic across a clean run (`errors=0`, no crash — this is a
silent wrong-answer, not an exception).

## Suspected root cause (not confirmed against source beyond what's quoted
above — no `src/` edits made, out of scope for lane RIS1)

`self.symbols` is presumably a `Dict<i64, Symbol>` (or similarly bracket-
indexed structure) keyed by raw id. If ordinary (non-import-pre-registration)
symbol allocation starts ids at 1 and reserves 0 as an internal "no symbol"
convention elsewhere in the codebase, while the 2-pass import
pre-registration path (module_lowering.spl / resolve_import_symbols) starts
its own id counter at 0, the two numbering schemes collide: a real, validly
registered symbol at id 0 becomes indistinguishable from "absent" wherever
that 0-reserved convention is assumed (possibly inside `Dict` bracket-index
itself for a missing key, returning a zero/nil default rather than truly
looking it up — see `doc/07_guide/language/dict_native_pitfallcs.md` for the
broader native-Dict pitfall family, though this reproduced under the
**interpreter**, not native codegen, so may be a distinct root cause).

## Impact on this lane

`resolve_import_symbols_spec.spl`'s "named import from module A wins over
same-named symbol from module B" example is left red (not weakened) pending
this fix. The example's harness plumbing (module_surfaces wiring, `.?`
matcher usage) is otherwise correct — see
`doc/08_tracking/bug/resolve_import_symbols_spec_field_and_wiring_repair_2026-07-29.md`.

## Related

- `doc/07_guide/language/dict_native_pitfalls.md` — sibling family of
  id/sentinel collision bugs in native Dict, though this one reproduces under
  the tree-walk interpreter
- `reference_jit_option_i64_value3_none_collision` (session memory) — same
  shape of bug (a legitimate small-integer payload colliding with a
  none/invalid sentinel), different site
