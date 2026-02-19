# Plan: test/ Directory Refactor — Mirror src/ Structure

**Date:** 2026-02-19
**Status:** Draft
**Related:** `doc/plan/src_refactor_lib_rename_2026-02-19.md`

---

## Core Design Decision

`test/` mirrors `src/`: every test subtree lives under `unit/`, `feature/`, or `integration/`,
then under the same sub-namespace as the source it tests (`app/`, `compiler/`, `compiler_core/`,
`compiler_shared/`, `lib/`).

- **`test/unit/`** — isolated unit tests, one class/module at a time
- **`test/feature/`** — end-to-end feature/system tests; **generates `doc/feature/`** docs on every run
- **`test/integration/`** — cross-component integration tests

1,434 AI-generated stub files (16 directories, `check(true)` everywhere) are deleted first.
Remaining ~2,880 real tests are re-homed.

---

## Documentation Generation

`test/feature/` tests drive automatic documentation output:

| Generated file | Trigger |
|----------------|---------|
| `doc/feature/feature.md` | Every `bin/simple test` run |
| `doc/feature/pending_feature.md` | Every `bin/simple test` run |

The existing `doc/feature/` is already the target — no path changes needed, only the source
directory is renamed from `test/system/` to `test/feature/`.

---

## Current State Summary

| Directory | Files | Status |
|-----------|-------|--------|
| `test/unit/` | 1,177 | Good — keep, minor re-homes |
| `test/system/` | 1,335 | Rename → `test/feature/` |
| `test/feature/` | 233 | Existing feature tests — absorb into new `test/feature/` |
| `test/integration/` | 41 | Keep shell, reorganize inside |
| `test/lib/` | 23 | Standalone project tests → `test/feature/lib/` |
| `test/compiler/` | 4 | Misplaced feature tests → `test/feature/compiler/` |
| `test/shared/` | 18 | Shared helpers — keep |
| `test/fixtures/` | 25 | Keep |
| `test/benchmarks/` | 5 | Merge into `test/perf/` |
| `test/perf/` | 3 | Keep |
| `test/baremetal/` | 4 | Fold into `test/feature/baremetal/` |
| `test/fuzz/` | 3 | Keep |
| `test/manual/`, `examples/`, `deploy/` | 3 | Keep |
| **AI-generated junk (16 dirs)** | **1,434** | **DELETE** |

---

## Target `test/` Structure

```
test/
  unit/
    app/              # mirrors src/app/         (was test/unit/app/)
      debug/
        remote/       # mirrors src/app/debug/remote/  (was test/unit/remote/)
    compiler/         # mirrors src/compiler/    (was test/unit/compiler/)
      lexer/          # was test/unit/lexer/ (3 files)
      parser/         # was test/unit/parser/ (28 files)
      type/           # was test/unit/type/ (2 files)
    compiler_core/    # mirrors src/compiler_core/  (was test/unit/compiler_core/)
    compiler_shared/  # mirrors src/compiler_shared/ (was test/unit/compiler_shared/)
    lib/              # mirrors src/lib/ (MERGED: test/unit/std/ + test/unit/lib/)
    baremetal/        # mirrors src/baremetal/    (was test/unit/baremetal/)
    runtime/          # runtime quirks            (was test/unit/runtime/)
    bugs/             # regression tests          (was test/unit/bugs/)

  feature/                          # ← generates doc/feature/ on every test run
    app/              # was test/system/app/ + test/feature/app/ (merge)
      mcp/            # was test/system/app/mcp/
    compiler/         # was test/system/compiler/ + test/compiler/ (4 files added)
      sample/         # was test/system/compiler/sample/
    lib/              # NEW: was test/lib/ (23 files)
    baremetal/        # was test/system/baremetal/ + test/baremetal/ (4 files)
    dap/              # was test/system/dap/
    ffi/              # was test/system/ffi/
    interpreter/      # was test/system/interpreter/
      sample/         # was test/system/interpreter/sample/
    io/               # was test/system/io/
    platform/         # was test/system/platform/
    watcher/          # was test/system/watcher/
    usage/            # was test/feature/usage/ (existing feature usage tests)

  integration/
    app/              # real integration tests for app/ code
    compiler/         # real integration tests for compiler/ code
    lib/              # real integration tests for lib/ code

  fixtures/           # keep
  shared/             # shared test helpers — keep
  perf/               # merged: test/perf/ + test/benchmarks/ (8 files total)
  fuzz/               # keep
  manual/             # keep
  examples/           # keep
  deploy/             # keep
```

**Deleted from `test/` root:** `app_complete/`, `app_extended/`, `compiler_complete/`,
`compiler_deep/`, `core_complete/`, `core_integration/`, `core_system/`, `lib_complete/`,
`lib_extended/`, `performance_stress/`, `resilience/`, `security/`, `stdlib_complete/`,
`stdlib_deep/`, `stdlib_improved/`, `integration_e2e/`, `mcp/` (empty), `integration/spec/` (empty)

---

## Phased Execution

### Phase T0 — Delete AI-generated junk (1,434 stubs, 16 dirs)

All files in these directories are trivial stubs (`check(true)`, `check(cmd.len() > 0)`).
They provide zero test coverage and inflate the test count.

```bash
rm -rf test/app_complete/        # 25 files
rm -rf test/app_extended/        # 75 files
rm -rf test/compiler_complete/   # 100 files
rm -rf test/compiler_deep/       # 174 files
rm -rf test/core_complete/       # 22 files
rm -rf test/core_integration/    # 50 files
rm -rf test/core_system/         # 1 file
rm -rf test/lib_complete/        # 33 files
rm -rf test/lib_extended/        # 74 files
rm -rf test/performance_stress/  # 33 files
rm -rf test/resilience/          # 2 files
rm -rf test/security/            # 1 file
rm -rf test/stdlib_complete/     # 200 files
rm -rf test/stdlib_deep/         # 200 files
rm -rf test/stdlib_improved/     # 429 files
rm -rf test/integration_e2e/     # 15 files (all check(true) stubs)
rm -rf test/mcp/                 # 0 files (empty dir)
rm -rf test/integration/spec/    # 0 files (empty dir)
```

**Impact:** 1,434 files deleted, 0 real tests lost.

---

### Phase T1 — Consolidate misplaced unit tests

Move loose unit subdirectories into their proper parent:

```bash
# test/unit/lexer/ → test/unit/compiler/lexer/
mv test/unit/lexer test/unit/compiler/lexer

# test/unit/parser/ → test/unit/compiler/parser/
# NOTE: test/unit/compiler/parser/ already exists with 6 files
# Move non-conflicting files, check conflicts manually
mv test/unit/parser/*.spl test/unit/compiler/parser/
rmdir test/unit/parser/

# test/unit/type/ → test/unit/compiler/type/
mv test/unit/type test/unit/compiler/type

# test/unit/remote/ → test/unit/app/debug/remote/
# (mirrors src/remote/ → src/app/debug/remote/ rename in git status)
mkdir -p test/unit/app/debug/remote
mv test/unit/remote/*.spl test/unit/app/debug/remote/
rmdir test/unit/remote/
```

**Files moved:** 3 + 28 + 2 + 6 = 39 files
**Import updates:** None required (unit tests import from `use app.debug.remote.*` already after src rename)

**Conflict check for parser merge:**
- `test/unit/compiler/parser/` already has: `parse_error_spec.spl`, `parse_formats_spec.spl`, `parser_new_spec.spl`, `parser_outline_spec.spl`, `parser_step_spec.spl`, `treesitter_spec.spl` (6 files)
- `test/unit/parser/` has 28 files with different names — verify no name collisions before move.

---

### Phase T2 — Parallel to src Phase 2: `shared_compiler` merge

No test files currently import `shared_compiler.*` directly, but verify:

```bash
grep -r "shared_compiler" test/unit/compiler_shared/ test/unit/compiler/
```

If any imports found, update `use shared_compiler.interpreter.` → `use compiler_shared.interpreter.`
(matches same change in 4 src files).

---

### Phase T3 — Parallel to src Phase 6: `std` → `lib` rename

After `src/std/` is renamed to `src/lib/`:

#### 3a. Check for parser/ name conflicts

```bash
# Before merging, list files in both dirs:
ls test/unit/std/parser/
ls test/unit/lib/  # no parser/ subdir here, so no conflict
```

#### 3b. Merge `test/unit/std/` into `test/unit/lib/`

`test/unit/std/` currently has: `contracts/`, `dl/`, `exp/`, `failsafe/`, `feature_validation/`,
`hooks/`, `improvements/`, `infra/`, `parser/`, `platform/`, `report/`, `units/`

`test/unit/lib/` currently has: `collections/`, `database/`, `diagnostics/`, `game_engine/`,
`lms/`, `mcp_sdk/`, `ml/`, `physics/`, `pure/`, `torch/`

No subdirectory name conflicts — safe to move all:

```bash
# Move all std subdirs into lib/
for d in contracts dl exp failsafe feature_validation hooks improvements infra parser platform report units; do
  mv test/unit/std/$d test/unit/lib/$d
done
rmdir test/unit/std/
```

#### 3c. Update imports in moved files

All files in (formerly) `test/unit/std/` that import `use std.*`:
→ No change needed (namespace stays `std.*` per src refactor — `src/lib/` maps to `std.*` namespace)

All files in `test/unit/lib/` that import `use lib.*`:
→ Update to `use std.*` (matches src Phase 6e: 106 `use lib.X` → `use std.X`)

```bash
# Count affected test files:
grep -rl "use lib\." test/unit/lib/ | wc -l
```

---

### Phase T4 — Rename `test/system/` → `test/feature/`

The entire `test/system/` tree becomes `test/feature/`. The existing `test/feature/` content
(233 files, subdirs `app/` and `usage/`) is merged in.

#### 4a. Rename the tree

```bash
mv test/system test/feature_new
```

#### 4b. Merge existing `test/feature/` into renamed tree

`test/feature/` currently has `app/` and `usage/` subdirs. The new `test/feature_new/` also
has `app/`. Merge the existing `app/` content:

```bash
# Merge existing feature/app/ into new feature/app/
cp -r test/feature/app/* test/feature_new/app/
# Move usage/ (no conflict)
mv test/feature/usage test/feature_new/usage
# Move any root-level .spl files from old feature/
mv test/feature/*.spl test/feature_new/ 2>/dev/null || true
rmdir test/feature/
mv test/feature_new test/feature
```

**Conflict check:** Verify no filename collisions between `test/feature/app/` and `test/system/app/`
before the merge.

#### 4c. Move `test/compiler/` → `test/feature/compiler/`

```bash
mv test/compiler/backend test/feature/compiler/backend
mv test/compiler/linker  test/feature/compiler/linker
rmdir test/compiler/
```

4 files moved. No import changes.

#### 4d. Move `test/lib/` → `test/feature/lib/`

`test/lib/` is a standalone project (has `.simple/build/`) with integration-style tests
for the std/lib packages. After the src rename it tests `src/lib/`:

```bash
mkdir -p test/feature/lib
mv test/lib/std      test/feature/lib/std
mv test/lib/mcp      test/feature/lib/mcp
mv test/lib/mcp_lib  test/feature/lib/mcp_lib
mv test/lib/*.spl    test/feature/lib/
mv test/lib/app      test/feature/lib/app
mv test/lib/compiler test/feature/lib/compiler
mv test/lib/core     test/feature/lib/core
mv test/lib/json     test/feature/lib/json
mv test/lib/lib      test/feature/lib/lib
rmdir test/lib/
```

23 files moved. Update `simple.sdn` if `test/lib` was a registered project path.

#### 4e. Merge `test/baremetal/` → `test/feature/baremetal/`

```bash
mv test/baremetal/*.spl test/feature/baremetal/
rmdir test/baremetal/
```

4 files moved.

---

### Phase T5 — Merge perf/benchmarks

```bash
mv test/benchmarks/*.spl test/perf/
mv test/benchmarks/README.md test/perf/
rmdir test/benchmarks/
```

5 files moved (total `test/perf/` becomes 8 files).

---

### Phase T6 — Reorganize `test/integration/`

Current `test/integration/` has 41 files but `test/integration/spec/` is empty.
Check what's actually in those 41 files:

```bash
find test/integration -name "*.spl" | head -20
```

Based on content, sort into:
- `test/integration/app/` — integration tests for app/ code
- `test/integration/compiler/` — integration tests for compiler/ code
- `test/integration/lib/` — integration tests for lib/ code

This phase is content-dependent; defer until Phase T4 is complete and the full file list is reviewed.

---

## File Movement Summary

| From | To | Files |
|------|----|-------|
| `test/unit/lexer/` | `test/unit/compiler/lexer/` | 3 |
| `test/unit/parser/` | `test/unit/compiler/parser/` | 28 |
| `test/unit/type/` | `test/unit/compiler/type/` | 2 |
| `test/unit/remote/` | `test/unit/app/debug/remote/` | 6 |
| `test/unit/std/` | `test/unit/lib/` (merge) | ~subdirs |
| `test/system/` | `test/feature/` (rename) | 1,335 |
| `test/feature/` (old) | `test/feature/` (merge) | 233 |
| `test/compiler/` | `test/feature/compiler/` | 4 |
| `test/lib/` | `test/feature/lib/` | 23 |
| `test/baremetal/` | `test/feature/baremetal/` | 4 |
| `test/benchmarks/` | `test/perf/` | 5 |
| **DELETED (AI junk)** | | **1,434** |

**Total real files moved/renamed: ~1,643**
**Total files deleted: 1,434**
**Net change: -1,434 stub files, 0 real test coverage lost**

---

## Coordination with src/ Refactor

| src Phase | Triggers test change |
|-----------|---------------------|
| Phase 2 (shared_compiler merge) | Verify `test/unit/compiler_shared/` imports — Phase T2 |
| Phase 6 (std→lib rename) | Merge `test/unit/std/` + `test/unit/lib/` — Phase T3 |
| Phase 6e (`use lib.*` → `use std.*`) | Same replacement in `test/unit/lib/` — Phase T3c |
| All phases | `bin/simple test` must pass after each |

**Sequence:** T0 and T1 can proceed independently of src/ phases.
T2 is gated on src Phase 2. T3 is gated on src Phase 6. T4–T6 are independent.

---

## Open Questions

1. **`test/lib/` project config** — Does `simple.sdn` list `test/lib` as a separate project? If so, update the path to `test/feature/lib` in Phase T4d.
2. **`test/unit/parser/` conflicts** — Confirm no filename collisions with existing `test/unit/compiler/parser/` before T1 merge.
3. **`test/feature/app/` merge conflict** — Check for filename collisions between existing `test/feature/app/` (233-file tree) and `test/system/app/` before T4b merge.
4. **`test/integration/` content** — Review the 41 actual files before deciding app/compiler/lib split in T6.
5. **`test/unit/runtime/`** — 3 files testing runtime quirks. Keep as-is or merge into `test/unit/lib/`?
6. **`test/shared/`** — Shared test utilities (18 files). Keep at `test/shared/` or move to `test/fixtures/`?

---

## Verification

After each phase:
```bash
bin/simple build          # Check compilation
bin/simple test           # Run all tests
```

After T0 (deletes): test count should drop by ~1,434; no failures.
After T3 (std→lib merge): `grep -r "use lib\." test/unit/lib/` should return 0 results.
After T4 (rename): `doc/feature/feature.md` still generates correctly.
