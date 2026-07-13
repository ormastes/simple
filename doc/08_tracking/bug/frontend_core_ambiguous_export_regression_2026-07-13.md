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
| `is_alpha` (+`is_alpha_num`) | `aop_predicate_parser.spl` (local helper, l.112) vs `lexer_chars.spl` | lexer_chars | rename the aop-local helper → `aop_is_alpha`/`aop_is_alpha_num` (only used inside that file, l.54/57/122). **VERIFIED clears the ambiguity** (native-build of a trivial closure passes; simpleos_tool build advances to the next symbol). Fix saved: `scratchpad/lanebx_recover/`-adjacent / this session's WC edit. |
| `mono_cache_register` | `monomorphize.spl` vs `type_erasure.spl` | (unverified) monomorphize | make the non-canonical definition file-private or import the shared one |
| `intersection_type_get_members` | `type_checker.spl` vs `types.spl` | (unverified) types | same pattern (found by Lane BX) |

Fix each the same way: keep ONE package-level definition (the canonical
module), make the duplicate file-private (rename with a module prefix) or
import the canonical one. Then re-run a `native-build --source src/compiler`
until it advances past module load — expect more instances until the cascade
clears.

## Ownership / why not fixed here

These live in `src/compiler/10.frontend/core` (central-compiler) and the same
parallel session that introduced them (`050209d9b36`) owns the in-progress
bootstrap redeploy — it hits these in its OWN bootstrap and will clear the
whole class. Landing piecemeal renames into the actively-churning tree risks
conflicting with that fix, and does NOT unblock the in-guest interpreter RUN
(that is blocked deeper — see below). So this is filed for the redeploy owner;
the `is_alpha` fix pattern above is verified and trivially applied to the rest.

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
