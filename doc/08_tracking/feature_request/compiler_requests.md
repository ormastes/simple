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
- **Status:** Open
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
- **Related-design-doc:** tbd — likely `src/compiler/10.frontend/` or
  `src/compiler/00.common/` name-resolution / symbol-table pass
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
