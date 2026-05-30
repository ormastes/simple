# Bug: macro `intro let` variable bindings evaluate to nil; `intro fn` works

**Date:** 2026-05-30
**Severity:** Medium (6 macro validation tests remain failing; fn-intro path is unaffected)
**Affects:** `test/feature/usage/macro_validation_spec.spl`
**Status:** Resolved 2026-05-30

## Symptom

All tests that invoke a macro with an `intro result: enclosing.module.let <name>: <T>` contract
and then access the introduced variable after emission produce `expected nil to equal <value>`.
The introduced variable is never bound into the caller's scope.

```
bin/simple run test/feature/usage/macro_validation_spec.spl 2>&1

Intro Shadowing Detection
  ✗ succeeds when intro introduces different symbol
    expected nil to equal 42

Type Annotation Requirements
  ✗ succeeds when intro let has type annotation
    expected nil to equal 42

Multiple Macros Ordering
  ✗ allows using macros in any order after definition
    expected nil to equal 2

Multiple Intro Symbols
  ✗ allows single intro symbol
    expected nil to equal 42

Intro For Loop
  ✗ generates symbols from const for loop
    expected nil to equal 2

Intro Conditional
  ✗ selects symbols based on const condition
    expected nil to equal 1
```

## Contrast: `intro fn` works

The `QIDENT Template Validation` group uses `enclosing.module.fn "get_{NAME}"() -> i64` intro
with a matching `emit result: fn ...` body. This passes:

```
QIDENT Template Validation
  ✓ succeeds with const parameter in template   # get_value() == 42 -- works
```

The contract/emit structure is identical between the two; only the intro kind differs:
`enclosing.module.fn` materialises correctly, `enclosing.module.let` does not.

## Root cause (hypothesis)

The interpreter's macro expansion path in `macro_registry.spl` processes `contract_intros`
and calls `expand_name_pattern` to compute symbol names, but the subsequent scope-injection
step for `IntroducedSymbol` records carrying a `let`/variable kind is either not reached or
deposits the value into an internal table that is never merged back into the interpreter's
environment frame at the call site. The `fn` path has a working injection because function
definitions are hoisted into the module-level symbol table by a separate mechanism.

Secondary observation: the compiler emits a spurious "Common mistake detected: Use 'val'/'var'"
info-lint for every `enclosing.module.let` line inside an intro contract block. The lint does
not recognise the intro DSL context and treats `let` as a misuse of the JavaScript `let`
keyword. This lint is cosmetic but may mislead future developers into changing the intro syntax.

## Repro steps

```bash
bin/simple run test/feature/usage/macro_validation_spec.spl 2>&1
# → 6 failures, all "expected nil to equal <N>"

# Passing contrast (fn intro works):
# see "succeeds with const parameter in template" test in the same file
```

## Failing tests (6)

| Test | describe group | Expected value |
|------|---------------|----------------|
| succeeds when intro introduces different symbol | Intro Shadowing Detection | 42 |
| succeeds when intro let has type annotation | Type Annotation Requirements | 42 |
| allows using macros in any order after definition | Multiple Macros Ordering | 2 |
| allows single intro symbol | Multiple Intro Symbols | 42 |
| generates symbols from const for loop | Intro For Loop | var_0==0, var_1==1, var_2==2 |
| selects symbols based on const condition | Intro Conditional | 1 |

## Impact

- 6 tests in `test/feature/usage/macro_validation_spec.spl` are permanently failing
  until the interpreter implements let-kind symbol injection for macro intro
- `intro let` is unusable at the call site in interpreter mode; `intro fn` is functional
- The file already carries a related TODO comment (line ~208):
  "Multi-intro macro gensym creates suffixed names (var1_gensym_1) — Need to resolve macro
  hygiene for multi-intro to expose clean names"
- Do NOT weaken or skip these tests; they correctly describe the intended behaviour

## Resolution

Fixed in the Rust seed interpreter macro expansion path by carrying runtime
values for `introduced_vars` out of the hygienic macro-local environment and
registering those values at the caller scope. Template substitution now also
resolves string/f-string binding patterns used by macro-generated identifiers,
which covers `val "var_{i}" = i` inside const-unrolled emit blocks.

Verification:

```bash
cargo check -p simple-compiler --manifest-path src/compiler_rust/Cargo.toml
cargo build -p simple-driver --manifest-path src/compiler_rust/Cargo.toml
SIMPLE_LIB=src src/compiler_rust/target/debug/simple run test/feature/usage/macro_validation_spec.spl
SIMPLE_LIB=src src/compiler_rust/target/debug/simple check test/feature/usage/macro_validation_spec.spl
```
