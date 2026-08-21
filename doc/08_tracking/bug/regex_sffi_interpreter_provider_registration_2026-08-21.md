# Regex SFFI interpreter provider registration gap

**Date:** 2026-08-21
**Status:** Fixed
**Severity:** High

## Symptom

The checked regex SFFI regression spec compiles and executes, but the
interpreter rejects calls to `rt_regex_new` and `rt_regex_is_match_quick` with
`semantic: unknown extern function`. One invalid-handle case that does not
invoke the provider passes.

## Reproduction

```text
bin/simple test test/01_unit/app/io/regex_sffi_spec.spl --mode=interpreter
```

Initial result: 5 examples executed, 1 passed, 4 failed. After adding typed
registry entries backed by a generation-checked slab, the same spec passes all
5 examples with the rebuilt interpreter.

## Required fix

Generate interpreter registration for the regex symbols from the canonical
SFFI registry and make absence a typed provider-admission error. Do not add a
weak implementation, fabricated return, per-call symbol lookup, or test skip.

## Performance constraint

Resolve and cache typed function pointers at admission. The hot path must not
perform hashing, registry lookup, string lookup, or allocation beyond the
regex operation itself.

## Resolution evidence

- `cargo test --manifest-path src/compiler_rust/compiler/Cargo.toml interpreter_extern::regex::tests --lib`: 2 passed.
- Rebuilt `src/compiler_rust/target/debug/simple` interpreter spec: 5 passed,
  0 failed.
- Boolean handle calls borrow their text argument and perform an O(1)
  generation/index lookup under a shared read lock. They do not allocate,
  dynamically resolve a symbol, or perform string-key/hash lookup.
