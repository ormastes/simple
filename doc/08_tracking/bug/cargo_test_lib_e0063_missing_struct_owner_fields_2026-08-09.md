# cargo test -p simple-compiler --lib does not compile — 9 × E0063 (2026-08-09)

**Status:** FIXED
**Severity:** High (blocked all Rust unit-test verification repo-wide)
**Area:** `src/compiler_rust/compiler/src/pipeline/native_project`

## Symptom

On pristine `origin/main` (d5ddc4371dd), the Rust unit-test target failed to build:

```
cargo test -p simple-compiler --lib --no-run
error[E0063]: missing fields `struct_module_owners` and `unique_struct_owners`
              in initializer of `native_project::ModuleImports`   (× 8)
error[E0063]: missing fields `struct_module_owners` and `unique_struct_owners`
              in initializer of `ImportMapResult`                 (× 1)
error: could not compile `simple-compiler` (lib test) due to 9 previous errors
```

Multiple agents hit this the same day and fell back to end-to-end link/build
evidence because the unit-test suite could not be run at all.

## Root cause

Mechanical test drift. `ModuleImports` (`native_project/mod.rs:236`) and
`ImportMapResult` (`native_project/imports.rs:9`) both gained two cross-module
nominal-layout lookup indices:

- `unique_struct_owners` — bare type name → canonical owner (unique names only)
- `struct_module_owners` — resolved declaration path → canonical module-prefix owner

Production construction sites were updated; the 9 test-only struct literals in
`native_project/tests.rs` were not. Neither struct derives `Default`, so there
was no spread fallback to absorb the addition.

## Sites (all in `src/compiler_rust/compiler/src/pipeline/native_project/tests.rs`)

`ModuleImports` literals at lines 305, 5215, 5327, 5467, 5605, 5675, 5739, 6457;
`ImportMapResult` literal in `empty_import_map_result()` at line 7122.

## Fix

Added the two missing fields as empty maps at each site, immediately after the
existing `struct_defs` field, matching the all-empty style already used by every
other field in these literals:

- `ModuleImports` (Arc-wrapped fields):
  `unique_struct_owners: std::sync::Arc::new(std::collections::HashMap::new()),`
  `struct_module_owners: std::sync::Arc::new(std::collections::HashMap::new()),`
- `ImportMapResult` (plain fields):
  `unique_struct_owners: std::collections::HashMap::new(),`
  `struct_module_owners: std::collections::HashMap::new(),`

Empty is the semantically correct value here: these are pure lookup indices, and
every one of these tests already constructs an otherwise all-empty import
environment (stub-object generation, fingerprint stability). None of them
exercises cross-module nominal-layout recovery, so an empty index preserves the
behaviour they were written to assert. `empty_import_map_result()` is explicitly
documented as "an all-empty `ImportMapResult`", so empty is what it must be.

## Note on the original report

The report that surfaced this also named
`src/compiler_rust/compiler/src/interpreter_call/block_execution.rs:1061` as an
E0063 site. It is not — that line is an unrelated
`warning: value assigned to \`last_value\` is never read`, adjacent in the compiler
output. All 9 E0063 errors were in `tests.rs`.

## Verification

`cargo test -p simple-compiler --lib --no-run` now succeeds. The suite runs:
3,500+ tests pass, including both tests that directly construct the literals this
change touched — `native_project_extra_provider_resolves_symbol_and_suppresses_stub`
(the `ModuleImports` literal at line 305) and
`test_cross_module_layout_fingerprint_sensitivity_and_stability` (which consumes
`empty_import_map_result`). Both are `ok`, so the empty-index choice preserves
what they assert.

Failures remain across the suite (HIR lowering, codegen, and ~37
`native_project` runtime-bundle / runtime-archive discovery tests). These are
**not attributable to this change** — they depend on built runtime artifacts in
`target/`, and there is no "before" baseline for any of them because the target
did not compile at all until this fix. They need separate triage now that the
suite is runnable again.

## Prevention

Consider `#[derive(Default)]` on `ImportMapResult` plus a test-only
`ModuleImports::empty()` constructor, so a future field addition updates one
place instead of nine.
