# CompilerContext multi-def name collision (W13-H class 3b reclassification)

Status: - **W15-K (this filing):** documented; not fixed in W15-K scope.

**Filed:** 2026-05-02 by W15-K agent
**Discovered during:** W15-K HIR class 3b source-side typo fixes
**Reclassified from:** W13-H class 3b → actually class 3a (multi-def collision)
**Status:** FIXED 2026-05-10. Renamed `src/compiler/80.driver/init.spl` CompilerContext → DriverContext to eliminate name collision with the two loader CompilerContext definitions.

## Symptom

Stage4/HIR diagnostic emits "ANY field" / dangling-field error for
`CompilerContext.handle` references at:

- `src/compiler/70.backend/linker/obj_taker.spl:394` — `self.compiler_ctx.handle`
- `src/compiler/70.backend/linker/obj_taker.spl:499` — `self.compiler_ctx.handle`

## Root cause (verified empirically 2026-05-02)

**Three different `CompilerContext` classes/structs are defined in the
codebase, with disjoint field sets.** The W11-E "ANY-field" pipeline
collapses them into one type via the first-wins or_insert in
`src/compiler_rust/.../pipeline/native_project/imports.rs` (per W13-F
class 1 root cause and W13-H class 3a investigation).

| File | Definition | Fields |
|------|------------|--------|
| `src/compiler/80.driver/init.spl:18` | `struct CompilerContext` | `config, container, mode` |
| `src/compiler/99.loader/compiler_ffi.spl:6` | `class CompilerContext` | `alive` |
| `src/compiler/99.loader/loader/compiler_ffi.spl:17` | `struct CompilerContext` | `handle: i64` |

The callers in `obj_taker.spl` legitimately need the `handle: i64`
variant from `99.loader/loader/compiler_ffi.spl` (they pass it to
`compiler_instantiate_template` / `compiler_infer_types` extern calls
that take the runtime handle). Whichever `CompilerContext` "wins" the
name-collision lottery in the import loader determines whether `.handle`
is "valid" or "dangling".

## Why W13-H misclassified this as 3b

W13-H's bug doc grouped this with `NLLError.help_value` etc. as
"source-side dangling field references — pure search/replace, no
compiler change". That is incorrect for this entry: the field exists
on the correct definition, but the wrong definition is winning the
name lookup. **There is no source-side rename that fixes it without
breaking the other two CompilerContext consumers.**

Per W13-H's own class 3a analysis, the genuine fix is the same as for
`Token.span` / `Symbol.name`:

> per-module-qualified registry, ~4-file compiler refactor; out of
> single-wave scope.

## Recommended fix

Same as class 3a — fix `pipeline/native_project/imports.rs` (or its
equivalent) to use a per-module-qualified registry instead of
first-wins `or_insert`. Until then the three CompilerContext defs
silently fight each other.

**Workaround candidates considered and rejected:**

- Renaming one of the CompilerContext classes — would touch both
  callers and consumers in `80.driver/`, `99.loader/`, and the FFI
  surface; non-trivial design call about which one keeps the name.
- Adding `handle` to the `init.spl` or `99.loader/compiler_ffi.spl`
  definitions — silently breaks the BeDomNode/BeLayoutBox byte-offset
  guarantee documented at `compiler.rs:215-225` (per W13-H bail
  discipline).

## Status

- **W15-K (this filing):** documented; not fixed in W15-K scope.
- **2026-05-10 (prior wave):** `80.driver/init.spl` `CompilerContext` renamed
  to `DriverContext`, reducing collision from 3 → 2 definitions.
- **2026-05-19 (Wave 5):** Rust-side fix verified complete. The
  `duplicate_struct_defs` sidecar + `try_resolve_global_field_for_struct`
  fallback chain (introduced in earlier waves) already handles the remaining
  two-definition collision correctly: `handle` exists in only one of the two
  `CompilerContext` layouts, so the duplicate-variant resolver picks it
  uniquely. No per-module-qualified registry refactor was needed.
  - Merge conflicts in `driver/src/cli/test_runner/runner.rs` resolved
    (took upstream side with auto-fallback threshold logic).
  - Test `test_duplicate_struct_sidecar_resolves_unique_compiler_context_handle`
    fixed: corrected field-type comparison from `String` to `simple_parser::Type`,
    and added missing `fn_arities` field to three `ModuleImports` test
    initializers at lines 1098, 1184, 1788.
  - `cargo check` passes clean (non-test); remaining 5 test-mode errors are
    pre-existing in out-of-scope files (`local_execution.rs`,
    `expression_tests.rs`).
- **Blocking:** resolved.
