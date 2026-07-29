# `resolve_import_symbols_spec.spl` was RED from three stacked spec-authoring bugs, not a product regression

**Status:** fixed (spec repaired; 4 of 8 examples now reveal separate real
product defects — see Related)
**Found:** 2026-07-29 (lane RIS1, mission-critical robustness campaign)
**Area:** `test/01_unit/compiler/hir/resolve_import_symbols_spec.spl` only —
no `src/` changes
**Severity:** n/a (test-authoring defect, not a product defect)

## Background

Lane CLSM flagged (2026-07-29) that `resolve_import_symbols_spec.spl` was
8/8 red because it referenced a stale `hir.errors` field — `HirModule` has
no `errors` field; errors live on the `HirLowering` object
(`hir_lowering.errors`). Lane RIS1 repaired the spec. Fixing that one field
reference was necessary but not sufficient — two more independent
spec-authoring bugs were stacked underneath it, each masking the next until
fixed.

## Bug 1: `hir.errors` -> `lowering.errors`

`HirLowering.lower_module(module) -> HirModule` — the returned `HirModule`
carries symbols/functions/classes but not diagnostics. Every
`expect(hir.errors.len()).to_equal(0)` was changed to
`expect(lowering.errors.len()).to_equal(0)`, and the "binds the mutable me
receiver" example's inline
`HirLowering.with_filename("me_receiver").lower_module(module)` was split
into a `var lowering = ...` + `lowering.lower_module(module)` so the
lowering object stays addressable for its `.errors`.

## Bug 2: `lowering.modules_by_name = <dict>` is a dead field assignment

7 of 8 examples wired cross-module test fixtures via:

```simple
var lowering = HirLowering.with_filename(path)
lowering.modules_by_name = modules_map   # Dict<text, any>
```

**`HirLowering` has no `modules_by_name` field.** Its actual cross-module
state is `module_surfaces: ModuleSurfacesByName` (see
`src/compiler/20.hir/hir_lowering/module_surface.spl`), built via
`module_surfaces_from_modules(modules: Dict<text, Module>, sources: [SourceFile])`
— this is exactly the pattern `driver.spl` uses (~line 967, ~line 1210) before
constructing `HirLowering` via `hirlowering_for_module(filename,
module_surfaces)`.

The interpreter silently accepts the assignment to a nonexistent field (no
compile error, no warning) and the resolver never saw any of the fixture
modules — every cross-module lookup failed. All 7 examples using this
pattern were rewritten to build a real `ModuleSurfacesByName` (via a small
per-file helper, `resolve_import_symbols_spec_build_surfaces`, that mirrors
`driver.spl`'s own wiring) and construct `HirLowering` with
`hirlowering_for_module(path, surfaces)` instead.

## Bug 3: `expect(x.?).to_equal(true)` is the wrong matcher for `.?`

12 assertions across the file used
`expect(hir.symbols.lookup(name).?).to_equal(true)` to mean "this symbol was
found." Per `doc/07_guide/quick_reference/syntax_quick_reference.md` §
"Existence Check (`.?`) — Returns `T?`", `.?` is **documented and confirmed**
to return `T?` (pass-through: the value if present, `nil` if absent) — it is
NOT a boolean predicate. Confirmed empirically:

```simple
val x: i64? = Some(5)
print x.?          # prints "5", not "true"
val s: SymbolId? = Some(SymbolId(id: 7))
print s.?           # prints "SymbolId(id: 7)", not "true"
```

So `expect(x.?).to_equal(true)` can only ever pass if the wrapped value is
literally the boolean `true` — for `SymbolId`/`i64` payloads it always fails
once the underlying lookup actually starts finding real symbols (which it
couldn't, before Bug 2 was fixed — so this bug was silently masked until
Bug 2's repair). Per `.claude/rules/testing.md`, `to_be_truthy()` /
`to_be_falsy()` are the correct matchers for `.?`'s documented "truthiness of
`T?`" boolean-context behavior. All 12 occurrences of
`.?).to_equal(true)` were changed to `.?).to_be_truthy()`.

## Net result

```
Results: 8 total, 4 passed, 4 failed
```

4 examples pass cleanly after the repair. The remaining 4 failures are real,
independently-verified product defects in HIR import resolution/lowering —
NOT spec bugs — each filed separately:

- `doc/08_tracking/bug/frontend_single_item_use_braces_import_crash_2026-07-29.md`
- `doc/08_tracking/bug/hir_get_symbol_id_zero_returns_nil_2026-07-29.md`
- `doc/08_tracking/bug/hir_qualified_import_call_statement_dropped_2026-07-29.md`

One additional example ("binds the mutable me receiver in a prefixed class
method") is flaky — pass/fail non-deterministic across repeated runs of the
identical repaired spec (observed 2 pass / 1 fail across 3 consecutive runs,
failing run showed `expected 2 to equal 0` i.e. 2 `unresolved name: me`
lowering errors). This is consistent with the previously-tracked
`doc/08_tracking/bug/stage4_me_receiver_unresolved_in_class_methods_2026-07-27.md`
(receiver-aliasing gap) but the non-determinism itself was not previously
documented and was not root-caused within this lane's budget.

## Related

- `test/01_unit/compiler/hir/class_method_bodies_reachable_spec.spl` —
  reference harness pattern this repair followed (inline
  parse-lower-per-example, no shared pipeline helper)
- `doc/08_tracking/bug/stage4_me_receiver_unresolved_in_class_methods_2026-07-27.md`
