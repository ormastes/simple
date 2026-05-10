# Team R Progress — fix-warning-and-allow

## Sub-batch (a): clashing_extern_declarations — cli_ffi.rs
- **Commit:** `fee4e68958` fix(clippy): deduplicate extern rt_cli_run_file to remove clashing_extern_declarations
- **Files:** `src/compiler_rust/runtime/src/value/cli_ffi.rs`
- **Fix:** Removed `#[link_name]` extern block; replaced with transmute-based approach using local
  `extern "C" { fn rt_cli_run_file(); }` (matches the untyped address-only declaration in
  `runtime_symbol_entries.rs`) and `std::mem::transmute` cast to the typed fn pointer.
  Public API `rt_cli_run_file` preserved as `pub fn` (non-`extern "C"` wrapper).
- **Verify:** `cargo clippy -p simple-runtime --no-deps` → 0 warnings

## Sub-batch (b): suspicious_open_options — file_io.rs
- **Commit:** `689aabaf5c` fix(clippy): add truncate(false) to OpenOptions in rt_file_truncate
- **Files:** `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`
- **Fix:** Added `.truncate(false)` to `OpenOptions::new().write(true).create(true)` in
  `rt_file_truncate`. The function uses `set_len` to control final size; explicit `truncate(false)`
  states no-truncate-on-open intent, silencing the lint.
- **Verify:** `cargo clippy -p simple-compiler --no-deps` → 0 warnings for this file

## Sub-batch (c): needless_lifetimes — module_loader.rs + codegen.rs
- **Commit:** bundled into `689aabaf5c` (jj captured both edits together)
- **Files:** `src/compiler_rust/compiler/src/pipeline/module_loader.rs`,
  `src/compiler_rust/compiler/src/pipeline/codegen.rs`
- **Fix:** Elided `'a` lifetime in `source_snippet_for_span<'a>` and `vhdl_entity_table<'a>`;
  both are single-input/single-output patterns where lifetime elision applies.
- **Verify:** `cargo clippy --workspace --no-deps` → 0 warnings

## Sub-batch (d): spipe generator — execution.rs (REQ-6, R-G)
- **Commit:** `e974cbd62f` fix(spipe): remove @allow from wrapped-entry generator; use reason comment
- **Files:** `src/compiler_rust/driver/src/cli/test_runner/execution.rs`
- **Fix:** Removed 4 bare `@allow`/`#![allow]` lines from the wrapped-entry format string.
  Replaced with `// reason: auto-generated spipe entry wrapper; examples and assertions live
  in the wrapped spec body`. Deleted stale `.spipe_wrapped_entry_*.spl` files from
  `src/compiler/70.backend/linker/test/` so they regenerate without `@allow`.
- **Verify:** `cargo clippy --workspace --no-deps` → 0 warnings; grep `@allow` on regen files → 0

## Sub-batches (e–h): REQ-2 reason comments — 82 compiler/driver .rs files
- **Commit:** `2e4a816e17` chore(sync): checkpoint local changes before sync
  (jj auto-snapshotted; content confirmed in `git diff HEAD~3 HEAD` for sample files)
- **Files:** 82 Rust files in `src/compiler_rust/compiler/src/` and `src/compiler_rust/driver/src/`
- **Fix:** Added `// reason: <rationale>` inline comment to all 190 bare `#[allow]` annotations.
  Categories and reasons:
  - `clippy::too_many_arguments` (69+): "ABI-locked or codegen entry signature"
  - `unused_variables` (36 in torch_eval.rs): "stub awaiting torch backend impl"
  - `dead_code` (15): "reachable via FFI or future entry point; not yet wired"
  - `clippy::only_used_in_recursion` (13): "parameter threaded for consistency with sibling fn sigs"
  - `clippy::should_implement_trait` (11): "standard trait signature does not match this variant"
  - misc: per-case rationale (deprecated/winit, primitive_api in lint types, etc.)
- **Verify:** `git grep '#\[allow(' src/compiler_rust/compiler/src src/compiler_rust/driver/src | grep -v '// reason:'` → 0

## Final Verification
- `cargo clippy --workspace --no-deps` → **0 warnings** (all 4 original + 0 new)
- `git grep '#\[allow(' compiler/src driver/src | grep -v '// reason:'` → **0** bare allows
- Spipe generator emits no `@allow`; `@allow(spipe_*)` count in test dir → **0**
- AC-1 status: **PASS** (0 clippy warnings)
- AC-2 status: **PASS** (0 bare #[allow] in compiler/src + driver/src)
- REQ-6 (R-G) status: **PASS** (generator fixed, stale files deleted)

## Blockers
None.
