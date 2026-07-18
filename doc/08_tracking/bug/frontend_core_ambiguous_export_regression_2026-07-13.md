# Regression: ambiguous package exports in `10.frontend/core/__init__.spl` break all fresh native-builds

**Status: ROOT-FIXED + VERIFIED (2026-07-18, lane Q3, `a79a52ba817`).** The
false-ambiguity mechanism described below was already fixed by commits
`b1efbf95bfe` and `e2edf611653f` (2026-07-13/14, both ancestors of the current
tip): `discovery.rs`'s package-export-owner resolution now tiers candidates
(`explicit re-export > real definition > imported facade > extern
re-declaration`) instead of treating every same-named provider as an equal
tie. Lane Q3 did not need to author a new fix — it added missing regression
coverage and verified the real production package resolves cleanly. See
"Root-fix verification (lane Q3)" below.

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

## Root-fix verification (lane Q3, 2026-07-18)

The regression's mechanism: `discovery.rs`'s package-owner resolution
(`src/compiler_rust/compiler/src/pipeline/native_project/discovery.rs`, the
bare-`export name` loop around line 900-1043) originally counted every sibling
file that merely *mentioned* a requested export name (a stale `extern fn`
forward re-declaration, or a plain `use` importer) as an equal "provider,"
tying against the file with the real `fn`/`struct`/... definition and
aborting the whole native-build with `ambiguous package export`. Commits
`b1efbf95bfe` and `e2edf611653f` fixed this by classifying each sibling into
four tiers — `explicit` (re-exports the name via `export use ...`),
`definitions` (a real `fn`/`class`/`struct`/... body), `facades` (a bare
`export` sibling that merely imports the name), `extern_weak` (a stale
`extern fn` re-declaration) — and picking the highest non-empty tier as sole
owner (`provided_export_names` / the tiered `owners` selection,
`discovery.rs:115-193` and `:987-1043`). A tie *within* the same tier (two
real, different `fn` definitions sharing a name) still correctly errors.

This lane confirmed the three known instances are fixed in the current tree
(`is_alpha` only defined in `lexer_chars.spl`; `mono_cache_register` only in
`monomorphize.spl`; `intersection_type_get_members` defined once in
`types.spl`, imported — not `extern`-redeclared — by `type_checker.spl`), and
added the regression coverage the fix previously lacked in
`src/compiler_rust/compiler/src/pipeline/native_project/tests.rs`:

- `test_entry_closure_bare_export_prefers_definition_over_stale_extern` —
  reproduces the historical bug shape (real `fn` + stale sibling `extern fn`
  re-declaration of the same bare-exported name) and asserts `discover_files`
  succeeds.
- `test_entry_closure_bare_export_rejects_genuine_duplicate_definitions` —
  negative control: two sibling files each with a real, different `fn`
  definition of the same exported name must still fail with `ambiguous
  package export` (proves the fix does not hide true ambiguity).
- `test_entry_closure_real_frontend_core_package_has_no_ambiguous_export` —
  runs `discover_files` against the actual
  `src/compiler/10.frontend/core/__init__.spl` (449 bare exports, 48 sibling
  files) at repo HEAD, proving the *production* package — the bug's literal
  subject — resolves with zero ambiguous-export errors, not just a synthetic
  reproduction.

Verified at `a79a52ba817` (working tree, prior to this lane's commit):

```
$ cargo test -p simple-compiler --lib -- \
    pipeline::native_project::tests::test_entry_closure_bare_export_prefers_definition_over_stale_extern \
    pipeline::native_project::tests::test_entry_closure_bare_export_rejects_genuine_duplicate_definitions \
    pipeline::native_project::tests::test_entry_closure_real_frontend_core_package_has_no_ambiguous_export \
    --exact
running 3 tests
test pipeline::native_project::tests::test_entry_closure_bare_export_prefers_definition_over_stale_extern ... ok
test pipeline::native_project::tests::test_entry_closure_bare_export_rejects_genuine_duplicate_definitions ... ok
test pipeline::native_project::tests::test_entry_closure_real_frontend_core_package_has_no_ambiguous_export ... ok
test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 3366 filtered out; finished in 1.26s
```

This closes the bug as scoped (the `core` package's ambiguous-export
false-positive). It does not touch the unrelated "Current boundary" note
below (strict linker) or the "Related, deeper blocker" (cranelift enum
miscompile) — those remain open, separate issues.

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
