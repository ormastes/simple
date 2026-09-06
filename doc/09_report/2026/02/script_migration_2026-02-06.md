# Python/Bash to Simple Migration Report

**Date:** 2026-02-06
**Status:** Phase 1 Complete (3/4) + Phase 5 Complete (Cleanup)
**Goal:** Migrate all Python/Bash scripts to Simple, except 3 bootstrap scripts

---

## Executive Summary

Migrating 25+ scripts (~3,000+ lines) from Python/Bash to Simple (.spl) to achieve 100% Simple implementation. Only 3 critical bootstrap scripts will remain as Bash.

**Progress:** 3/25 scripts migrated (12%)
**Archived:** 18 obsolete scripts (Phase 5 complete)

---

## Bootstrap Scripts (KEEP as .sh)

These MUST remain as Bash because they run before Simple runtime exists:

- ✅ `scripts/build-bootstrap.sh` - GitHub Actions first build
- ✅ `scripts/build-full.sh` - Release package builder
- ✅ `scripts/install.sh` - End-user installer (curl | sh)

---

## Phase 1: Quick Wins (High Impact, Low Complexity)

**Target:** 1-2 days | **Status:** 75% complete

| Script | Status | Target Location | Lines |
|--------|--------|-----------------|-------|
| `scripts/build/link-bins.sh` | ✅ **DONE** | `src/app/build/link_bins.spl` | 40 |
| `scripts/jj-wrappers/git.sh` | ⏸️ **SKIP** | (Keep as-is per user) | 73 |
| `scripts/build/run_quick_tests.sh` | ✅ **DONE** | `src/app/test/quick_runner.spl` | ~100 |
| `scripts/build/capture_bootstrap_debug.sh` | ✅ **DONE** | `src/app/build/capture_debug.spl` | ~50 |

**Completed:**
- ✅ Created `src/app/utils/colors.spl` (145 lines) - ANSI color utilities
- ✅ Migrated `link-bins.sh` → `link_bins.spl` (97 lines)
- ✅ Migrated `run_quick_tests.sh` → `quick_runner.spl` (203 lines)
- ✅ Migrated `capture_bootstrap_debug.sh` → `capture_debug.spl` (97 lines)
- ✅ Created test files: `link_bins_spec.spl`, `colors_spec.spl`

**Skipped:**
- `git.sh` - Keep as Bash per user request

---

## Phase 2: Build Tools (Medium Complexity)

**Target:** 3-4 days | **Status:** Not started

| Script | Status | Target Location | Lines |
|--------|--------|-----------------|-------|
| `scripts/fix_ffi_calls.py` | ⏳ TODO | `src/app/audit/ffi_analyzer.spl` | 206 |
| `scripts/build/scaffold_feature_test.py` | ⏳ TODO | `src/app/test/scaffold.spl` | 283 |
| `scripts/build/extract_tests_from_spec.py` | ⏳ TODO | `src/app/test/extract.spl` | 340 |
| `scripts/build/spec_gen.py` | ⏳ TODO | `src/app/doc/spec_gen/` (module) | 992 |

**Required Utilities:**
- ⏳ `src/app/utils/markdown.spl` - MarkdownBuilder, table formatting
- ⏳ `src/app/utils/parsing.spl` - Section extraction, table parsing
- ⏳ `src/app/utils/text_replace.spl` - Regex patterns, bulk replacements

---

## Phase 3: Verification Tools (High Complexity)

**Target:** 2-3 days | **Status:** Not started

| Script | Status | Target Location | Lines |
|--------|--------|-----------------|-------|
| `scripts/verify/verify_features.sh` | ⏳ TODO | `src/app/verify/features.spl` | 254 |
| `scripts/verify/verify_doctest.sh` | ⏳ TODO | `src/app/verify/doctest.spl` | ~50 |
| `scripts/verify/verify_generic_syntax.sh` | ⏳ TODO | `src/app/verify/generics.spl` | ~80 |
| `scripts/verify/test_visibility.sh` | ⏳ TODO | `src/app/verify/visibility.spl` | ~60 |

---

## Phase 4: Advanced Tools (Lower Priority)

**Target:** 2-3 days | **Status:** Not started

| Script | Status | Target Location | Lines |
|--------|--------|-----------------|-------|
| `scripts/build/download-mold.sh` | ⏳ TODO | `src/app/build/linker/download_mold.spl` | 162 |
| `scripts/build/setup-dashboard-ci.sh` | ⏳ TODO | `src/app/ci/setup_dashboard.spl` | ~200 |
| `scripts/build/cpu-aware-test.sh` | ⏳ TODO | `src/app/test/cpu_aware.spl` | ~150 |
| `scripts/profiling/profile-interpreter.sh` | ⏳ TODO | `src/app/profiling/profile.spl` | ~100 |

---

## Phase 5: Migration Tools (Archive)

**Target:** 1 day cleanup | **Status:** ✅ COMPLETE

**Action:** Move obsolete migration scripts to `archive/scripts/`

| Script | Status |
|--------|--------|
| `scripts/migrate/*.py` (8 files) | ✅ Archived to `archive/scripts/migrate/` |
| `scripts/migrate/*.sh` (5 files) | ✅ Archived to `archive/scripts/migrate/` |
| `scripts/migrate/*.spl` (2 files) | ✅ Archived to `archive/scripts/migrate/` |
| `scripts/build/link-bins.sh` | ✅ Archived (replaced by `link_bins.spl`) |
| `scripts/build/run_quick_tests.sh` | ✅ Archived (replaced by `quick_runner.spl`) |
| `scripts/build/capture_bootstrap_debug.sh` | ✅ Archived (replaced by `capture_debug.spl`) |
| `scripts/prepare-release.sh` | ⏳ TODO: Migrate to `src/app/release/prepare.spl` |

**Archived:** 18 obsolete scripts to `archive/scripts/`
**Deleted:** Empty `scripts/migrate/` directory

---

## New Files Created (Phase 1)

### Utility Modules
- `src/app/utils/colors.spl` (145 lines)
  - ANSI color codes and terminal formatting
  - Semantic colors: success, error, warning, info
  - Color stripping utility

### Migrated Scripts
- `src/app/build/link_bins.spl` (97 lines)
  - Creates symlinks from bin/rust/ to bin/simple/
  - Validates source files exist before linking
  - Color-coded output

- `src/app/test/quick_runner.spl` (203 lines)
  - Runs first N test files with timeout
  - Tracks pass/fail/crash/timeout stats
  - Detailed logging with timestamps

- `src/app/build/capture_debug.spl` (97 lines)
  - Captures bootstrap debug output
  - Extracts phase 3, compile, and AOT debug messages
  - Timestamped log files

### Test Files
- `test/app/build/link_bins_spec.spl` (23 lines)
- `test/app/utils/colors_spec.spl` (33 lines)

**Total New Code:** ~598 lines of Simple

---

## SFFI Functions Used

All required capabilities available in `src/app/io/mod.spl`:

**File Operations:**
- `file_exists()`, `file_read()`, `file_write()`, `file_append()`
- `file_delete()`, `file_size()`

**Directory Operations:**
- `dir_create(path, recursive)`, `dir_list()`, `is_dir()`
- `dir_remove(path, recursive)`

**Process Execution:**
- `process_run(cmd, args)` → `(stdout, stderr, exit_code)`
- `process_run_timeout(cmd, args, timeout_ms)`
- `shell(command)` → `ProcessResult`

**Environment/System:**
- `cwd()`, `home()`, `env_get()`, `getpid()`
- `timestamp_year()`, `timestamp_month()`, etc.
- `current_time_unix()`

**No gaps found** - all necessary functions exist!

---

## Testing Strategy

For each migrated script:

1. **Unit Tests:** SSpec tests in `test/app/<category>/`
2. **Integration Tests:** Run against real files (temp directories)
3. **Regression Tests:** Compare output with original script
4. **Manual Verification:** Run in development before committing

---

## Success Criteria

- [ ] 25+ scripts migrated to Simple (3/25 = 12%)
- [x] 3 bootstrap scripts identified and preserved
- [x] Utility modules created (colors.spl)
- [ ] Zero workflow regressions
- [ ] CLAUDE.md updated with strict policy
- [ ] All tests passing
- [ ] CI workflows updated
- [ ] Migration guide documented

---

## Next Steps

### Immediate (Phase 1 Completion)
1. ✅ Create `colors.spl` utility
2. ✅ Migrate `link-bins.sh`
3. ✅ Migrate `run_quick_tests.sh`
4. ✅ Migrate `capture_bootstrap_debug.sh`
5. ⏳ Test migrated scripts
6. ⏳ Update CLAUDE.md with explicit policy

### Phase 2 (Next)
1. Create `markdown.spl`, `parsing.spl`, `text_replace.spl` utilities
2. Migrate `fix_ffi_calls.py`
3. Migrate `scaffold_feature_test.py`
4. Migrate `extract_tests_from_spec.py`
5. Modularize and migrate `spec_gen.py`

---

## Risk Mitigation

**Risk:** Shell-specific features not available
**Mitigation:** Use `process_run()` or `shell()` for external commands

**Risk:** Performance regression
**Mitigation:** Benchmark before/after, optimize hot paths

**Risk:** Breaking CI workflows
**Mitigation:** Keep .sh and .spl side-by-side during testing

---

## Timeline Estimate

- Phase 1: 1-2 days (**75% complete**)
- Phase 2: 3-4 days
- Phase 3: 2-3 days
- Phase 4: 2-3 days
- Phase 5: 1 day

**Total:** 9-13 days (or incremental over 2-3 weeks)
