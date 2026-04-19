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
- **Suspected cause:**
  Shallow investigation (2026-04-18): `low_memory` (line 91) and `mode` (line 75)
  are plain struct fields on `CompileOptions` in
  `src/compiler/00.common/driver_core_types.spl` — they are **not** methods.
  The Rust-seed runtime generates field-getter stubs automatically; the
  self-hosted compiler's runtime dispatch appears to miss this auto-generation
  step for these fields (or for the `CompileOptions` struct specifically).
  Suspected areas:
  1. `src/compiler/80.driver/driver.spl` or `driver_api_types.spl` — compile-mode
     dispatch path that interprets field reads as method calls.
  2. Self-hosted codegen for struct field accessor lowering (likely in
     `src/compiler/70.backend/` or `src/compiler/10.frontend/`).
  3. The `driver_core_compile_options_default()` free function (line 142) is
     present; the issue is specifically field read dispatch on struct instances,
     not the constructor.
  No source edits were made. Fix is deferred to the compiler track.
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
  4. Observe "Runtime error: Function 'CompileOptions.low_memory' not found"
