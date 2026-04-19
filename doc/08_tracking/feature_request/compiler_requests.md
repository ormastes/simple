# Compiler Feature Requests

Secondary channel for feature requests against the Simple compiler
(`src/compiler/`). See `README.md` for the primary vs secondary channel rule.

- **Target:** compiler
- **Owning design doc:** `src/compiler/` (no single owning design doc; relevant
  sub-areas noted per entry)

## Schema

Entries use the fields in `TEMPLATE.md`:

| Field | Notes |
|-------|-------|
| id | `FR-COMPILER-####`, monotonic |
| title | verb-led, ≤ 80 chars |
| Filed-on | `YYYY-MM-DD` |
| Filed-by | author / agent / session id |
| Priority | `P0` / `P1` / `P2` (required at `Accepted`) |
| Status | `Open` / `Accepted` / `Implemented` / `Rejected` |
| Requested-semantics | one-paragraph description |
| Acceptance-criteria | observable bullets |
| Related-upfront | upfront doc §section, or `none` |
| Related-design-doc | design doc §section, or `tbd` |
| Related-issue | GH issue URL (optional) |
| Notes | blockers / alternatives / crash refs (optional) |

An entry may not move to `Implemented` without a `Related-design-doc` or
`Related-issue` link.

## Open Requests

### FR-COMPILER-002 — Fix self-hosted import resolver: same-named structs in different modules shadow each other

- **Filed-on:** 2026-04-18
- **Filed-by:** Claude Sonnet 4.6 / FR-COMPILER-001 investigation session
- **Target:** compiler — import resolver / name-resolution pass
- **Priority:** P0
- **Status:** Partially-Implemented (2026-04-18, Claude Sonnet 4.6)
- **Requested-semantics:**
  When two structs share the same short name but live in different fully-qualified
  module paths (e.g., `compiler.common.driver_core_types.CompileOptions` vs
  `compiler.backend.backend.backend_types.CompileOptions`), the self-hosted
  compiler's import resolver picks the wrong struct even when the caller uses an
  explicit `use compiler.common.driver_core_types.*` import. The Rust-seed
  bootstrap binary resolves the explicit import correctly. The self-hosted binary
  must resolve struct names according to the explicitly imported module namespace,
  not by last-seen or alphabetical order among all loaded modules.
- **Acceptance-criteria:**
  - [ ] `use compiler.common.driver_core_types.{CompileOptions}` followed by
        `val opts = CompileOptions.default(); print(opts.input_files.len().to_text())`
        succeeds in the self-hosted binary without "Function not found".
  - [ ] `use compiler.backend.backend.backend_types.{CompileOptions}` resolves to the
        7-field backend struct and does NOT expose `mode` / `low_memory`.
  - [ ] Both can be used in the same file via aliased imports without collision.
  - [ ] FR-COMPILER-001 acceptance criteria are met after this fix.
- **Related-upfront:** none
- **Related-design-doc:** tbd — `src/compiler/20.hir/hir_lowering/items.spl` and
  `src/compiler/20.hir/hir_types.spl`
- **Related-issue:** FR-COMPILER-001 (upstream symptom)
- **Notes:**
  Root cause confirmed by discriminator test (2026-04-18):
  - Bootstrap binary: `input_files`, `mode`, `low_memory`, `verbose`, `release`,
    `gc_off`, `debug_info` all resolve correctly on the 17-field driver struct.
  - Self-hosted binary: `input_files` (field unique to driver struct) fails first,
    proving the resolver silently picks the 7-field backend struct instead.
  The fix must be in the self-hosted import/symbol resolver. Renaming one of the
  two structs (e.g., `DriverCompileOptions` vs `BackendCompileOptions`) is a
  valid workaround but requires widespread callers update — prefer fixing the
  resolver so explicit `use` paths take precedence.

- **Deep-diagnosis (2026-04-18, Claude Sonnet 4.6):**

  **Two divergence points pinpointed:**

  **Divergence A — `src/compiler/20.hir/hir_lowering/items.spl:210-225`
  (`lower_import`):**
  The self-hosted `lower_import` produces a metadata `HirImport` record
  (module_path + items list) and returns. It does NOT walk the imported module's
  AST, does NOT call `symbols.define` for imported types, and does NOT create any
  scope binding for names brought in by the `use` statement. The import is
  recorded for later IR emission but has no effect on the live symbol scope during
  HIR lowering.

  Contrast with the Rust seed
  `src/compiler_rust/compiler/src/hir/lower/import_loader.rs`: it runs a
  two-pass import loading pipeline — `preregister_imported_type_names` (Pass 0.5a)
  registers empty placeholders for names from *each specific imported module's
  AST*, filtered by `should_import_symbol(target)` — then `load_imported_types`
  (Pass 0.5b) fills in full field lists via `register_named`/`register_struct`/
  `register_class` and inserts into `globals`. The explicit import target
  (`ImportTarget::Glob` for `use mod.*` or `ImportTarget::Named(names)` for
  selective imports) gates *which* module's struct wins.

  **Divergence B — `src/compiler/20.hir/hir_types.spl:201-245`
  (`SymbolTable.define` / `SymbolTable.lookup`):**
  `define()` at line 224 stores `scope_syms[name] = id` — keyed by the bare
  short name. When a second module's struct with the same short name is registered
  (e.g., via `declare_module_symbols` pulling in both loaded modules), the dict
  entry is overwritten. Last-write-wins; module load order determines which struct
  survives.

  The `Symbol` struct carries a `defining_module: text?` field (populated from
  `self.module_filename` at line 216), but `lookup()` at lines 230-245 walks the
  scope chain matching only on `name` — it never consults `defining_module` or the
  import list. The `module_filename` context is set once per `HirLowering`
  instance for the *current compilation unit's own file*
  (`HirLowering.with_filename(filename)`), not per imported module, so all symbols
  from all imported modules appear under the same `module_filename` value anyway —
  the disambiguation data is never written in the first place.

  **Combined effect:** Two `CompileOptions` structs compete in the same flat scope.
  `lower_import` does not register the explicitly-named import into scope, so the
  `use compiler.common.driver_core_types.*` declaration is a no-op on the symbol
  table. `lookup("CompileOptions")` returns whichever struct was last defined by
  `declare_module_symbols`, which is load-order-dependent.

  **Minimum repro (2-file + driver, no existing codebase needed):**
  ```
  # a_types.spl
  class Foo:
      only_in_a: i64

  # b_types.spl
  class Foo:
      only_in_b: i64

  # driver.spl
  use a_types.*
  val x = Foo(only_in_a: 1)
  print(x.only_in_a.to_text())   # fails "Function not found" in self-hosted
                                  # if b_types loads after a_types
  ```

  **Proposed fix direction:**
  Mirror the Rust seed's two-pass approach in the self-hosted HIR lowering.
  In `src/compiler/20.hir/hir_lowering/items.spl`, extend `lower_import` (or
  add a new `resolve_import_symbols` pass called from `lower_module` before body
  lowering) to: (1) load the imported module's AST, (2) filter by the import
  target (wildcard vs. named list), and (3) call `self.symbols.define` for each
  matching struct/class/enum, supplying the imported module's path as
  `defining_module`. In `src/compiler/20.hir/hir_types.spl`, update
  `SymbolTable.define` to refuse re-registration of an already-bound short name
  (i.e., first-write-wins, matching the Rust seed's `is_none()` guard in
  `preregister_imported_type_names`), so the explicit `use` path's types take
  precedence over any later load of a conflicting module.

  Do NOT attempt this fix here — dedicated compiler-core agent required.

- **Partial-fix applied (2026-04-18, Claude Sonnet 4.6):**
  Two minimal changes made within `src/compiler/20.hir/`:

  1. `hir_lowering/items.spl` — `lower_module` (and the bootstrap-safe
     `HirLowering_dot_lower_module`) now sets `self.module_filename = module.name`
     at entry, before `declare_module_symbols`. Previously the single shared
     `HirLowering` instance (instantiated once in `driver.spl` and reused for
     every module) always had `module_filename = ""`, so every symbol across all
     modules was tagged with an empty `defining_module`. Now each module's symbols
     carry the correct per-module name in `Symbol.defining_module`.

  2. `hir_types.spl` — `SymbolTable.define` now has a first-write-wins guard for
     type-kind symbols (Class/Struct/Enum/Trait): if the current scope already
     contains a binding for `name`, the existing `SymbolId` is returned unchanged.
     Non-type symbols (Function, Parameter, Field, Variable, etc.) retain
     last-write-wins behaviour so normal redefinition and shadowing continue
     to work.

  **What this fixes:** determinism — the first module processed "wins" the short
  name rather than the last. Module processing order is now deterministic
  (dict key iteration order in the driver loop).

  **What this does NOT fix:** import-target-aware resolution. If
  `driver_core_types.spl` loads AFTER `backend_types.spl` in the driver's module
  map, the first-write-wins guard means `backend_types.CompileOptions` wins and
  the bug persists. Full fix requires FR-COMPILER-003 (2-pass import resolver
  with per-import-target AST loading). Bootstrap is required to verify effect.

  **Infrastructure blocker confirmed:** `HirLowering` has no `module_resolver`,
  `current_file`, or `loaded_modules` fields. The Rust seed's two-pass approach
  (`preregister_imported_type_names` + `load_imported_types`) cannot be ported
  without first adding a module-resolver port to `HirLowering` — that is driver-
  layer work outside `src/compiler/20.hir/`.

---

### FR-COMPILER-003 — Add 2-pass import resolver to self-hosted HIR lowering

- **Filed-on:** 2026-04-18
- **Filed-by:** Claude Sonnet 4.6 / FR-COMPILER-002 fix session
- **Target:** compiler — `src/compiler/20.hir/hir_lowering/` + `src/compiler/80.driver/`
- **Priority:** P0
- **Status:** Open
- **Requested-semantics:**
  The self-hosted HIR lowerer (`HirLowering`) must mirror the Rust seed's
  two-pass import loading pipeline from
  `src/compiler_rust/compiler/src/hir/lower/import_loader.rs`:

  Pass 0 (`preregister_imported_type_names`): for each `use mod.*` or named
  import, resolve the module path to a `.spl` file, parse it, and register
  empty placeholder types for all exported names that match the import target.

  Pass 1 (`load_imported_types`): fill in field lists, method sets, and
  globals for the placeholders created in Pass 0, filtered by
  `should_import_symbol(target)`.

  Without this, `lower_import` is a metadata-only no-op that never calls
  `symbols.define` for imported names, so `use compiler.common.driver_core_types.*`
  has no effect on the symbol table and `CompileOptions` resolves by module
  load order rather than explicit import path.
- **Acceptance-criteria:**
  - [ ] `use compiler.common.driver_core_types.{CompileOptions}` followed by
        a field access on the 17-field driver struct succeeds in the self-hosted
        binary (FR-COMPILER-002 AC #1).
  - [ ] `use compiler.backend.backend.backend_types.{CompileOptions}` resolves
        to the 7-field backend struct and does NOT expose `mode` / `low_memory`
        (FR-COMPILER-002 AC #2).
  - [ ] Both can coexist in the same file via aliased imports (FR-COMPILER-002 AC #3).
  - [ ] FR-COMPILER-001 acceptance criteria are met.
- **Prerequisites (infrastructure changes needed first):**
  1. Add `module_resolver: ModuleResolverPort?` field to `HirLowering` class
     (currently absent — confirmed 2026-04-18).
  2. Add `current_file: text?` and `loaded_modules: [text]` fields to `HirLowering`.
  3. Driver (`src/compiler/80.driver/driver.spl`) must populate these fields when
     constructing `HirLowering` — i.e., `HirLowering.with_resolver(resolver, file)`.
  4. `lower_module` must call a new `resolve_import_symbols` pass before
     `declare_module_symbols` to pre-populate the scope with explicitly imported names.
- **Related-upfront:** none
- **Related-design-doc:** `src/compiler_rust/compiler/src/hir/lower/import_loader.rs`
  (reference implementation, 717 lines)
- **Related-issue:** FR-COMPILER-002 (parent), FR-COMPILER-001 (upstream symptom)
- **Notes:**
  FR-COMPILER-002 partial fix (first-write-wins + per-module `module_filename`)
  landed 2026-04-18. That fix is a prerequisite but does not resolve the
  import-target-awareness gap. This FR is the blocking item for FR-COMPILER-001.

---

### FR-COMPILER-001 — Fix self-hosted binary missing CompileOptions field accessors

- **Filed-on:** 2026-04-18
- **Filed-by:** Claude Sonnet 4.6 / FR-BENCH-CLOCK-001 verification session
- **Target:** compiler
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  The self-hosted release binary (`bin/release/x86_64-unknown-linux-gnu/simple`)
  fails to resolve `CompileOptions.low_memory` and `CompileOptions.mode` at
  runtime, producing "Function 'CompileOptions.low_memory' not found" and
  "Function 'CompileOptions.mode' not found" errors. The Rust-seed bootstrap
  binary (`src/compiler_rust/target/bootstrap/simple`) resolves both correctly
  for identical input. The self-hosted binary must resolve struct field accesses
  on `CompileOptions` (and any other struct) identically to the Rust seed,
  without falling through to "no mode matched" warnings.
- **Acceptance-criteria:**
  - [ ] `bin/release/x86_64-unknown-linux-gnu/simple /tmp/t_clock.spl` (3-line
        script: `extern fn rt_time_now_ns() -> i64` + `print(rt_time_now_ns().to_string())`)
        runs without "Function 'CompileOptions.*' not found" errors.
  - [ ] `[WARN] no mode matched, falling through` no longer appears for
        `CompileOptions` field reads.
  - [ ] Self-hosted binary output matches Rust-seed bootstrap binary output
        for the same input file.
- **Related-upfront:** none
- **Related-design-doc:** tbd
- **Related-issue:** none
- **Investigation (2026-04-18, Claude Sonnet 4.6):**
  Deep investigation performed. Root cause is **wrong-struct name collision**
  (root cause C — compiler-core bug). Two structs named `CompileOptions` exist:
  - `src/compiler/00.common/driver_core_types.spl` — 17-field driver struct
    with `mode`, `low_memory`, `input_files`, `verbose`, `release`, etc.
  - `src/compiler/70.backend/backend/backend_types.spl` — 7-field backend struct
    with `target`, `opt_level`, `debug_info`, `emit_assembly`, etc.
  The Rust-seed bootstrap resolves the import `use compiler.common.driver_core_types.*`
  correctly to the 17-field struct — all fields including `mode` and `low_memory`
  work. The self-hosted release binary resolves to the 7-field backend struct even
  with an explicit `use compiler.common.driver_core_types.*` import — fields
  unique to the driver struct (`input_files`, `mode`, `low_memory`, etc.) all fail
  as "Function not found"; fields in the 7-field set are silently resolved to the
  wrong struct. Confirmed with `/tmp/test_compile_options.spl` — `input_files`
  fails before `mode` and `low_memory`, proving it is not a selective gap.
  This is an import-resolution name-shadowing bug in the self-hosted compiler:
  when two structs share a name across different modules, the self-hosted resolver
  picks the wrong one regardless of explicit import path. See FR-COMPILER-002.
  No source edits made. Fix requires compiler-core surgery.
- **Notes:** Blocks pure-Simple end-to-end testing of any new `extern fn`
  (including `rt_time_now_ns`) via the self-hosted binary. Use
  `src/compiler_rust/target/bootstrap/simple` as workaround until resolved.
  Repro steps:
  1. `scripts/bootstrap/bootstrap-from-scratch.sh --deploy`
  2. Create `/tmp/t_clock.spl`:
     ```
     extern fn rt_time_now_ns() -> i64
     print(rt_time_now_ns().to_string())
     ```
  3. `bin/release/x86_64-unknown-linux-gnu/simple /tmp/t_clock.spl`
  4. Observe "Runtime error: Function 'CompileOptions.input_files' not found"
     followed by "Function 'CompileOptions.low_memory' not found" and
     "Function 'CompileOptions.mode' not found" — wrong-struct collision.
