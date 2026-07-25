# Regression: ambiguous package exports in `10.frontend/core/__init__.spl` break all fresh native-builds

**Introduced by** the parallel commit `050209d9b36` ("fix: speed up pure Simple
bootstrap") on origin/main. Breaks any `native-build` that loads the compiler
frontend (the seed's own bootstrap, `simpleos-native-build`, the multiarch
in-guest toolchain builds, CI). NOT WC-only — verified on origin tip.

## Symptom

`Build failed: ambiguous package export \`<name>\` in
src/compiler/10.frontend/core/__init__.spl: <fileA>, <fileB>` — a package
symbol is defined in two source files aggregated into the `core` package, so
the `__init__.spl` re-export can't disambiguate.

## Known instances (a class, likely more — a cascade)

| Symbol | Files | Canonical | Fix |
|---|---|---|---|
| `is_alpha` | `aop_predicate_parser.spl` vs `lexer_chars.spl` | `lexer_chars.spl` | **VERIFIED:** rename the semantically different AOP-local identifier helpers and source the public facade export. |
| `mono_cache_register` | `monomorphize.spl` vs `type_erasure.spl` | `monomorphize.spl` | **VERIFIED:** rename the incompatible type-erasure-local cache helper and source the public facade export. |
| `intersection_type_get_members` and seven sibling accessors | `type_checker.spl` stale externs vs `types.spl` | `types.spl` | **VERIFIED:** import the canonical named/union/intersection/refinement registry accessors and delete the extern providers. |

Keep one package-level owner. Import stale declarations from that owner; give
distinct private state a module-specific name. Never pick the first provider or
special-case a symbol in discovery.

## Current boundary

The next bounded continuation verified the monomorphization owner and cleared
the parser facade's duplicate compatibility paths by sourcing split expression
and statement APIs from their real modules. Native-build then passed package
discovery and compiled every source module. No ambiguous core export remains in
the current full-CLI closure; the strict linker now owns the next blocker.

## Related, deeper blocker (does not depend on this)

Even with all ambiguous exports fixed, the in-guest x86_64 Simple interpreter
still cannot run: the SEED's cranelift backend miscompiles enum single-`text`-
payload extraction in freestanding one-binary builds, so a parsed
`Call(callee=Ident("print"))` reads an EMPTY callee name → "unresolved name: "
at HIR lowering (`20.hir/hir_lowering/expressions.spl:197`). The seed lacks an
LLVM backend, so it is forced onto the buggy cranelift path. The unblock is the
#99 whole-compiler redeploy: build the in-guest toolchain with the pure-Simple
SELF-HOSTED compiler (no such miscompile), not the seed. See
`scratchpad/lanebx_recover/DIAGNOSIS_FINAL.md`.
