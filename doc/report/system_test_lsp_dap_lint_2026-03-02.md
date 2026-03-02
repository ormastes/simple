# System Test Suite: LSP + DAP + Lint on Full Codebase

**Date:** 2026-03-02
**Status:** Implemented and validated

## Overview

Intensive system tests that exercise LSP query, DAP debug, and lint operations against the full Simple codebase (~2,943 .spl files). Each test runs real subprocess calls (`bin/release/simple`) against every relevant source file to catch crashes, hangs, and regressions.

**Goal:** No LSP query, DAP operation, or lint run should crash (exit code > 1) on any source file.

## Test Inventory

| Group | Specs | Files Tested | Operations | Est. Time |
|-------|-------|-------------|------------|-----------|
| LSP | 9 | ~2,943 | 8 per file (~23,500 total) | ~2 hours |
| Lint | 3 | ~2,943 | 1 per file | ~30 seconds |
| DAP | 4 | ~300 (sampled) | lint parse | ~5 seconds |
| **Total** | **17** (incl. helper) | **~2,943** | **~26,700** | **~2 hours** |

## File Structure

```
test/system/
  helpers/
    batch_test_helpers.spl         # Reference: shared helper functions

  lsp/
    compiler_00_15_lsp_spec.spl    # 00.common + 10.frontend + 15.blocks
    compiler_20_35_lsp_spec.spl    # 20.hir + 25.traits + 30.types + 35.semantics
    compiler_40_60_lsp_spec.spl    # 40.mono + 50.mir + 55.borrow + 60.mir_opt
    compiler_70_lsp_spec.spl       # 70.backend (~186 files)
    compiler_80_99_lsp_spec.spl    # 80.driver + 85.mdsoc + 90.tools + 95.interp + 99.loader
    lib_common_lsp_spec.spl        # lib/common (~676 files)
    lib_nogc_sync_lsp_spec.spl     # lib/nogc_sync_mut
    lib_async_lsp_spec.spl         # nogc_async_mut + gc_async_mut + noalloc
    app_lsp_spec.spl               # src/app (~501 files)

  lint/
    compiler_lint_spec.spl         # All compiler layers (~1,412 files)
    lib_lint_spec.spl              # All lib modules
    app_lint_spec.spl              # All app modules (~501 files)

  dap/
    dap_breakpoint_system_spec.spl # DAP module parse + app file sample
    dap_stepping_system_spec.spl   # Interpreter + frontend modules
    dap_variables_system_spec.spl  # Type system + semantics modules
    dap_stack_trace_system_spec.spl# Loader + interpreter + driver modules
```

## LSP Operations Tested

Each LSP spec tests 8 subcommands on every file in its group:

| Subcommand | Needs Position | Tests |
|------------|---------------|-------|
| `hover` | Yes (first code line) | Type/doc info at symbol |
| `definition` | Yes | Jump-to-definition |
| `references` | Yes | Find all references |
| `completions` | Yes | Code completion |
| `semantic-tokens` | No (whole file) | Syntax highlighting |
| `folding-range` | No (whole file) | Code folding |
| `document-highlight` | Yes | Same-file occurrences |
| `type-definition` | Yes | Type navigation |

LSP queries run via: `bin/release/simple src/app/cli/query.spl <subcmd> <file> <line> [col]`

## Running the Tests

```bash
# Run individual spec
bin/simple test test/system/lint/app_lint_spec.spl

# Run all lint system tests (fast, ~30s)
bin/simple test test/system/lint/

# Run all DAP system tests (fast, ~5s)
bin/simple test test/system/dap/

# Run single LSP spec (~7-25 min depending on file count)
bin/simple test test/system/lsp/compiler_70_lsp_spec.spl

# Run ALL system tests (~2 hours)
bin/simple test test/system/lsp/ test/system/lint/ test/system/dap/
```

## Architecture

### Subprocess Testing Pattern

All tests use `rt_process_run()` to spawn real subprocesses:

```simple
extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)

fn run_lsp(subcmd: text, file: text, line: i64, col: i64) -> i64:
    val (stdout, stderr, code) = rt_process_run("bin/release/simple",
        ["src/app/cli/query.spl", subcmd, file, "{line}", "{col}"])
    code
```

### Crash Detection

- Exit code 0 = success
- Exit code 1 = not-found / normal error
- Exit code > 1 = crash (test failure)

### File Discovery

Recursive `.spl` file discovery via `rt_dir_list()`:

```simple
fn find_spl_files(dir: text) -> [text]:
    var result: [text] = []
    val entries = rt_dir_list(dir) ?? []
    # ... recurse into non-hidden entries
```

### Position Selection

For position-based LSP queries, `find_first_code_line()` finds the first non-comment, non-empty line in each file.

## Validation Results

| Spec | Files | Result | Time |
|------|-------|--------|------|
| lint/app_lint_spec | 501 | 0 crashes | 5.1s |
| lint/compiler_lint_spec | 1,412 | 0 crashes | ~15s |
| dap/breakpoint | 13 DAP + 51 app | 0 crashes | 1.8s |
| dap/stepping | 28 | 0 crashes | 0.4s |
| dap/variables | 79 | 0 crashes | 0.8s |
| dap/stack_trace | 111 | 0 crashes | 1.0s |
| lsp/* | ~2,943 × 8 ops | In progress | ~2 hours |

## Design Decisions

1. **Self-contained specs**: Each spec inlines all helper functions rather than importing from a shared module (test runner doesn't reliably resolve cross-test imports).

2. **No `tag:` on describe blocks**: The `tag: ["slow", "system"]` parameter on `describe` causes `it` blocks to be skipped by the test runner regardless of flags. Tags are documented in header comments only.

3. **DAP uses lint, not execution**: Running arbitrary .spl files via subprocess can hang on files with blocking main loops (REPL, servers). DAP specs verify module parsing via `bin/release/simple lint` instead.

4. **While loops in module-level functions**: All batch operations use `while` loops inside module-level functions (not inside `it` block closures) to avoid the closure mutation limitation.

## Key Files Referenced

| File | Role |
|------|------|
| `src/app/cli/query.spl` | LSP query CLI — 18+ subcommands |
| `src/app/cli/query_lsp_extras.spl` | Extra LSP ops |
| `src/compiler/90.tools/lint/main.spl` | Lint engine |
| `src/lib/nogc_sync_mut/dap/` | DAP server library |
