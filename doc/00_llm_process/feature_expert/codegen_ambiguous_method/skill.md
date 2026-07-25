# Codegen Ambiguous Method Feature Expert

## Role

Own feature-specific process knowledge for the `CODEGEN-AMBIGUOUS-METHOD` class
— a compiler resolver limitation where multiple same-named method candidates
cause the seed (Rust) to refuse codegen and stub a body, forcing interpreter
fallback. This is a known blocker for generic dispatch and method overloading.
Tracks workarounds, interpreter behavior, and resolution strategy.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)
- [impl skill](../../../../.claude/skills/impl/IMPL.md)

## Feature Links

- HIR resolver: [src/compiler/20.hir/hir_lowering/](../../../../src/compiler/20.hir/hir_lowering/)
  (method candidate resolution, CODEGEN-AMBIGUOUS-METHOD emission).
- Method dispatch in lowering: [src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl](../../../../src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl)
  (where stubbed bodies are detected).
- Tests: grep for `CODEGEN-AMBIGUOUS-METHOD` in test/ to find reproducers.
- Tracking: [doc/08_tracking/bug/](../../../../doc/08_tracking/bug/) (related
  resolver issues).

## Symptoms & Workarounds (2026-07-10 — landed 024456cbac4)

**Symptom:** Bare method call with >1 same-named candidate → seed refuses
codegen → stubs body → module-wide interpreter fallback (entire compilation
unit runs in interpreter, slow + limited debugging).

**Resolver facts:**
1. Typed local `val ct: T = x` works (same-function scope only). Type annotation
   disambiguates to the correct candidate.
2. FOR-LOOP VAR annotations are IGNORED — annotation syntax parsed but not
   applied at runtime. Workaround: declare a separate typed `val` in the loop
   body.
3. Dict-index type recovery only works for `self.field` dicts (struct member).
   Local dict indexing erases to ANY (loses type info). Direct `.get()` call
   loses type too.

**Workaround pattern:**
```
// BAD: ambiguous
fn foo(x: any) {
  x.to_text()  // multiple candidates → interpreter fallback
}

// GOOD: typed local
fn foo(x: any) {
  val ct: MyType = x  // annotation disambiguates
  ct.to_text()        // now resolved → native codegen
}

// For loops: GOOD
fn process(items: [any]) {
  for item in items {
    val typed_item: MyType = item  // separate val, not loop-var annotation
    typed_item.to_text()  // resolved
  }
}
```

## Gotchas

1. **Interpreter fallback is module-wide:** a single ambiguous method in any
   function in a module forces the ENTIRE module to run in interpreter. This
   is a perf cliff — even small helper functions become slow.
2. **Type annotations on loop vars are silent no-ops:** they parse without
   error but don't actually narrow the type at runtime. Always use a separate
   `val` declaration in the loop body.
3. **Local dict indexing erases to ANY:** `dict[key]` where `dict` is a local
   variable loses all type information, even if the dict's type is known. Only
   `self.field_dict[key]` (struct member dict) preserves type.

## Permanent Fix Status

**Blocker:** The resolver's type-narrowing strategy needs rework to track
generic instantiations and method dispatch at call sites without annotation
hints. This is a multi-week architecture change. No ETA.

**Mitigation (short-term):** Expand the typed-local heuristic to handle more
patterns (loop vars, dict accesses), document the current limits clearly.

## Update Rule

After any resolver changes, ambiguous-method refactors, or workaround
discoveries, refresh this skill with new patterns and permanent-fix progress.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
