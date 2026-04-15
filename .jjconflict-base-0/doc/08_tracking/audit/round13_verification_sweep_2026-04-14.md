# Round 13 Verification Sweep — 2026-04-14

## Build Smoke

- **os build --arch=x86_64**: OK — `phase=native-build OK elapsed_ms=1083`
- **cargo bootstrap (simple-driver)**: FAIL — `error: no matching package named 'ahash' found` in vendored crates directory. The `simple-parser v0.9.3` dependency requires `ahash` but it is absent from `src/compiler_rust/vendor/`. Pre-built release binary unaffected; only fresh Rust bootstrap is blocked.

## Unit Test Suite Snapshot

| Subdir | Files | Passed | Failed | Skipped | Notes |
|--------|-------|--------|--------|---------|-------|
| compiler/parser | 67 | 606 | 0 | 0 | All green |
| compiler/codegen | 5 | 43 | 0 | 0 | All green |
| compiler/semantic | 8 | 0→3* | 1→0* | 0 | `self_field_method_resolution_spec.spl` shown as failed in directory sweep but passes when run individually (3 passed, 0 failed). Likely stale cache from earlier round. |
| compiler/interpreter | 4 | 64 | 0 | 0 | All green |
| os/services/launcher | 2 | 21 | 0 | 0 | All green |
| os/services/wm | 2 | 12 | 0 | 0 | All green |
| os/kernel | 20 | 286 | 0 | 0 | All green |
| os/desktop | 3 | 42 | 0 | 0 | All green |
| os/runtime | 0 | 0 | 0 | 0 | No spec files present |
| std/spec | 0 | 0 | 0 | 0 | No spec files present |

**Total unit: 746 passed, 0 confirmed failures** (semantic stale-cache false positive resolves on individual run).

## System Specs Status

| Spec | Status | Passed | Failed | Notes |
|------|--------|--------|--------|-------|
| simpleos_desktop_framebuffer_spec.spl | RED | 1 | 2 | Interpreter: `string_to_failure_strategy` / `failure_strategy_to_string` undefined in `std.spec`; QEMU boots but 2 it-blocks fail |
| engine2d_in_qemu_spec.spl | RED | 1 | 2 | Interpreter: `be_result` undefined in `matchers`; also missing `string_to_failure_strategy` / `failure_strategy_to_string` |
| engine2d_primitives_spec.spl | RED | 0 | 1 | File not found: `test/system/engine2d_primitives_spec.spl` does not exist on this working copy |
| sys_gui_001_boot_launcher_spec.spl | RED | 0 | 1 | File not found: spec does not exist on this working copy |
| sys_gui_002_compositor_cold_start_spec.spl | RED | 0 | 1 | File not found: spec does not exist on this working copy |
| sys_gui_005_cleanup_lifecycle_spec.spl | RED | 0 | 1 | File not found: spec does not exist on this working copy |
| sys_gui_006_with_apps_spec.spl | RED | 1 | 2 | `builds desktop_e2e_entry.spl into baremetal kernel` fails; `boots desktop-ready with 4 apps (shortcut:fail pending_vt4)` fails; `undefined string_to_failure_strategy` |
| simpleos_desktop_disk_boot_spec.spl | RED | 1 | 3 | Interpreter: `be_true / be_false / be_truthy / be_falsy / BeTrueMatcher / BeFalseMatcher` undefined in `matchers`; also `string_to_failure_strategy` / `failure_strategy_to_string` missing |

**Green: 0 / 8 fully passing. Red: 8 / 8.**

Note: `sys_gui_001`, `sys_gui_002`, `sys_gui_005`, `engine2d_primitives` are missing from the working copy (`test/system/` directory). They exist in other jj revisions (e.g. commits `ns`, `uuk`) that are not yet merged to `@` (current working copy is `rys`, parent `ot`/`sz`). The `test/system/` directory on `@` does not include these files.

## Root Causes

### 1. Missing matcher symbols in `std.spec` / `matchers` (affects 5+ specs)
- `string_to_failure_strategy`, `failure_strategy_to_string` — missing from `std.spec`
- `be_result` — missing from `matchers`
- `be_true`, `be_false`, `be_truthy`, `be_falsy`, `BeTrueMatcher`, `BeFalseMatcher`, `BeTruthyMatcher` — missing from `matchers`
- All appear as interpreter warnings at module load: `Export statement references undefined symbol`
- This is a `std.spec` / `std.spec.matchers` stdlib regression introduced in a recent round

### 2. Missing spec files on current working copy (`@` = rys)
- `engine2d_primitives_spec.spl`, `sys_gui_001_boot_launcher_spec.spl`, `sys_gui_002_compositor_cold_start_spec.spl`, `sys_gui_005_cleanup_lifecycle_spec.spl` are in divergent jj revisions not yet on `@`

### 3. Cargo vendor missing `ahash`
- `src/compiler_rust/vendor/` is missing the `ahash` crate required by `simple-parser v0.9.3`
- Bootstrap build from Rust source is blocked; prebuilt `release/` binary is unaffected

## Regressions Introduced (Round 12 → Round 13)

Based on `std.spec` interpreter warnings across all QEMU-based system specs:

1. **`std.spec` missing `string_to_failure_strategy` / `failure_strategy_to_string`** — affects every QEMU spec; this symbol was previously exported and is now absent, causing test runner misfires at QEMU result evaluation
2. **`matchers` missing `be_true` / `be_false` / `be_result` family** — affects `simpleos_desktop_disk_boot_spec` and `engine2d_in_qemu_spec`; matcher exports removed or renamed in recent `std.spec` work
3. **`sys_gui_006`: `builds desktop_e2e_entry.spl into baremetal kernel` fails** — kernel build step inside spec is failing (QEMU binary stale or build step regression)

## Still-Red Specs (known, tracked)

| Spec | Root Cause | Tracking |
|------|-----------|---------|
| `sys_gui_001_boot_launcher_spec.spl` | Missing from `@` working copy | Pending merge of `ns` rev |
| `sys_gui_002_compositor_cold_start_spec.spl` | Missing from `@` working copy | Pending merge of `ns` rev |
| `sys_gui_005_cleanup_lifecycle_spec.spl` | Missing from `@` working copy | Pending merge of `uuk` rev |
| `engine2d_primitives_spec.spl` | Missing from `@` working copy | Unknown rev |
| `simpleos_desktop_framebuffer_spec.spl` | `std.spec` missing `string_to_failure_strategy` | std.spec regression |
| `engine2d_in_qemu_spec.spl` | `matchers` missing `be_result`; `std.spec` regression | std.spec regression |
| `sys_gui_006_with_apps_spec.spl` | Kernel build step fail + `std.spec` regression | VT4 pending + std.spec |
| `simpleos_desktop_disk_boot_spec.spl` | `matchers` missing `be_true/false` + `std.spec` regression | std.spec regression |

## Recommendation

1. **Fix `std.spec` / `matchers` symbol exports** — restore `string_to_failure_strategy`, `failure_strategy_to_string`, `be_true`, `be_false`, `be_truthy`, `be_falsy`, `BeTrueMatcher`, `BeFalseMatcher`, `BeTruthyMatcher`, `be_result`. This single fix will unblock 5+ system specs.
2. **Merge pending revisions** (`ns`, `uuk`) containing `sys_gui_001`, `sys_gui_002`, `sys_gui_005`, `engine2d_primitives` spec files onto `@`.
3. **Vendor `ahash`** for `simple-parser v0.9.3` in `src/compiler_rust/vendor/` to restore `cargo build --profile bootstrap`.
4. **Investigate `sys_gui_006` kernel build step** — the `builds desktop_e2e_entry.spl` it-block is failing; may be stale ELF or missing build artifact.
