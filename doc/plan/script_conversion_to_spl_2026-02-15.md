# Shell Script to Simple (.spl) Conversion Plan

**Goal:** Remove all `.sh` and `.bat` scripts except bootstrap-related. After bootstrap, all tooling runs as `.spl` or SSH commands.

**Status:** Phase 1 started (1/32 scripts converted)

---

## Classification

### KEEP - Bootstrap Scripts (3 files, ~1,356 lines)

These run BEFORE Simple compiler exists:

| Script | Lines | Purpose | Status |
|--------|-------|---------|--------|
| `script/bootstrap-from-scratch.sh` | 736 | Main bootstrap (Linux/macOS) | **KEEP** |
| `script/bootstrap-from-scratch-freebsd.sh` | 520 | FreeBSD bootstrap | **KEEP** |
| `script/bootstrap-from-scratch.bat` | ~100 | Windows bootstrap | **KEEP** |

---

## CONVERT - Post-Bootstrap Scripts (32+ files, ~5,700 lines)

### Phase 1: Test Infrastructure (Priority 1) - IN PROGRESS

| Script | Lines | .spl Equivalent | Status |
|--------|-------|-----------------|--------|
| `filter_pending_tests.sh` | 51 | `src/app/test/filter_pending.spl` | ✅ **DONE** |
| `ci-test.sh` | 293 | `src/app/test/ci_runner.spl` | 📝 PLANNED |
| `local-container-test.sh` | 328 | `src/app/test/container_test.spl` | 📝 PLANNED |
| `docker-test.sh` | 284 | `src/app/test/docker_runner.spl` | 📝 PLANNED |

**Completed:** 1/4 (25%)
**Total lines converted:** 51 → 116 lines .spl

### Phase 2: Build System (Priority 2)

| Script | Lines | .spl Equivalent | Status |
|--------|-------|-----------------|--------|
| `build-bootstrap.sh` | 285 | `src/app/build/bootstrap.spl` | 📝 PLANNED |
| `build-bootstrap-multi-platform.sh` | 143 | `src/app/build/multi_platform.spl` | 📝 PLANNED |
| `build-cross-compile-all.sh` | 263 | `src/app/build/cross_compile.spl` | 📝 PLANNED |
| `setup-bootstrap-binaries.sh` | 226 | `src/app/build/setup_bins.spl` | 📝 PLANNED |
| `install.sh` | 201 | `src/app/install/web_install.spl` | 📝 PLANNED |
| `build_custom_qemu.sh` | 165 | `src/app/build/qemu_builder.spl` | 📝 PLANNED |
| `build_type_database.sh` | ~50 | `src/app/build/type_db.spl` | 📝 PLANNED |
| `build-full.sh` | ~80 | `src/app/build/full.spl` | 📝 PLANNED |

**Total:** 8 scripts, ~1,413 lines

### Phase 3: Platform Testing (Priority 3)

| Script | Lines | .spl Equivalent | Status |
|--------|-------|-----------------|--------|
| `test-freebsd-qemu-setup.sh` | 548 | `src/app/test/freebsd_qemu_setup.spl` | 📝 PLANNED |
| `test-freebsd-qemu-basic.sh` | 405 | `src/app/test/freebsd_basic.spl` | 📝 PLANNED |
| `test-macos-self-hosting.sh` | 210 | `src/app/test/macos_selfhost.spl` | 📝 PLANNED |
| `verify-cross-builds.sh` | 182 | `src/app/verify/cross_builds.spl` | 📝 PLANNED |
| `verify-docker-setup.sh` | 174 | `src/app/verify/docker_setup.spl` | 📝 PLANNED |
| `verify-baremetal-setup.sh` | ~100 | `src/app/verify/baremetal.spl` | 📝 PLANNED |

**Total:** 6 scripts, ~1,619 lines

### Phase 4: Development Tools (Priority 4)

| Script | Lines | .spl Equivalent | Status |
|--------|-------|-----------------|--------|
| `migrate_tests.sh` | 1004 | `src/app/migrate/tests.spl` | 📝 PLANNED |
| `fix_bare_imports_simple.sh` | ~150 | `src/app/fix/imports.spl` | 📝 PLANNED |
| `fix_constructors_smart.sh` | ~150 | `src/app/fix/constructors.spl` | 📝 PLANNED |
| `configure_freebsd_vm_ssh.sh` | 119 | `src/app/setup/freebsd_ssh.spl` | 📝 PLANNED |
| `docker-build-test-runner.sh` | ~80 | `src/app/test/build_runner.spl` | 📝 PLANNED |
| `tools/fix_imports_correct.sh` | ~100 | `src/app/fix/imports_v2.spl` | 📝 PLANNED |

**Total:** 6 scripts, ~1,603 lines

### Phase 5: Specialized Tools (Priority 5)

| Script | Lines | .spl Equivalent | Status |
|--------|-------|-----------------|--------|
| `test_mcp_server.sh` | 88 | `src/app/mcp/test_server.spl` | 📝 PLANNED |
| `test_mcp_working.sh` | ~50 | `src/app/mcp/health_check.spl` | 📝 PLANNED |
| `benchmark/mcp_startup.sh` | ~100 | `src/app/perf/mcp_startup.spl` | 📝 PLANNED |
| `benchmark/mcp_startup_comparison.sh` | ~100 | `src/app/perf/mcp_compare.spl` | 📝 PLANNED |
| `examples/baremetal/build.sh` | 109 | `examples/baremetal/build.spl` | 📝 PLANNED |
| `examples/baremetal/build_*.sh` (4) | ~200 | `examples/baremetal/*.spl` | 📝 PLANNED |
| `examples/baremetal/test_*.sh` (3) | ~150 | `examples/baremetal/test_*.spl` | 📝 PLANNED |
| `seed/run_coverage.sh` | ~50 | `src/app/coverage/seed.spl` | 📝 PLANNED |

**Total:** 8+ scripts, ~847 lines

---

## Completed Conversions

### 1. filter_pending.spl ✅

**Original:** `script/filter_pending_tests.sh` (51 lines bash)
**New:** `src/app/test/filter_pending.spl` (116 lines Simple)
**Status:** Complete, tested

**Features:**
- Recursively finds all `*_spec.spl` files in target directory
- Checks for `# @pending` or `# @skip` markers
- Creates two output files:
  - `build/pending_tests.txt` - Exclusion list
  - `build/active_tests.txt` - Active test list
- Displays summary statistics (count, percentages)

**APIs used:**
- `file_read()`, `file_write()`, `file_exists()` - File I/O
- `dir_list()`, `is_dir()`, `dir_create_all()` - Directory ops
- `get_args()` - Command-line arguments
- `std.string.{starts_with, trim, ends_with}` - String utilities
- `std.path.{join}` - Path manipulation

**Key differences from bash:**
- Type-safe (catches errors at compile time)
- More verbose (explicit types, error handling)
- Cross-platform (works on Windows without modification)
- Better structured (clear function separation)

**Usage:**
```bash
# Old (bash)
./script/filter_pending_tests.sh test/lib

# New (Simple)
bin/simple run src/app/test/filter_pending.spl test/lib
```

---

## Available Simple APIs (All from `src/app/io/mod.spl`)

### Process Execution
- `process_run(cmd, args)` - Structured process execution
- `shell(cmd)` - Run shell command, get full result (stdout, stderr, exit_code)
- `shell_output(cmd)` - Get stdout only
- `shell_bool(cmd)` - Check success/failure
- `process_run_timeout()` - With timeout support

### File Operations
- `file_read()`, `file_write()`, `file_append()`
- `file_exists()`, `file_delete()`, `file_copy()`
- `file_lock()`, `file_size()`, `file_hash_sha256()`
- `file_read_lines()` - Read file as line array
- `file_atomic_write()` - Atomic file write

### Directory Operations
- `dir_create()`, `dir_create_all()`, `dir_list()`
- `dir_exists()` → `is_dir()`
- `dir_remove()`, `dir_remove_all()`
- `dir_walk()` - Recursive directory traversal

### Environment
- `env_get()`, `env_set()`, `env_vars()` - Environment variables
- `cwd()`, `home()` - Working directory, home directory
- `host_os()`, `host_arch()` - Platform detection

### System Info
- `getpid()`, `hostname()`, `cpu_count()`
- `current_time_unix()`, `current_time_ms()` - Time functions
- `thread_sleep()` - Sleep

### Missing APIs (Minor Gaps)

1. **Signal handling** - Need `process_kill(pid, signal)`
2. **TTY detection** - Need `is_tty(fd)`
3. **Process stdin pipe** - Need `process_run_stdin(cmd, input)`
4. **Glob patterns** - Could use `dir_walk()` + pattern matching

These can be added to `src/app/io/process_ops.spl` as needed.

---

## Conversion Patterns

### Pattern 1: Simple Shell Wrapper

**Bash:**
```bash
check_tool() {
    if ! command -v "$1" >/dev/null 2>&1; then
        echo "ERROR: $1 not found. $2"
        exit 1
    fi
}
```

**Simple:**
```simple
fn check_tool(cmd: text, msg: text):
    if not shell_bool("command -v {cmd}"):
        print "ERROR: {cmd} not found. {msg}"
        exit(1)
```

### Pattern 2: File Finding

**Bash:**
```bash
ALL_SPECS=$(find "$TARGET_DIR" -name "*_spec.spl" -type f)
```

**Simple:**
```simple
fn find_spec_files(dir: text) -> [text]:
    var results: [text] = []
    find_spec_files_recursive(dir, results)
    results

fn find_spec_files_recursive(dir: text, results: [text]):
    val entries = dir_list(dir)
    for entry in entries:
        val path = join(dir, entry)
        if is_dir(path):
            find_spec_files_recursive(path, results)
        else if ends_with(entry, "_spec.spl"):
            results.push(path)
```

### Pattern 3: Percentage Calculation

**Bash:**
```bash
PCT=$((COUNT * 100 / TOTAL))
```

**Simple:**
```simple
val pct = if total > 0:
    (count * 100) / total
else:
    0
```

### Pattern 4: Docker/Process Execution

**Bash:**
```bash
docker run --rm --memory=512m --cpus=1.0 simple-test:latest test
```

**Simple:**
```simple
fn run_in_container(image: text, memory: text, cpus: text, cmd: text):
    val full_cmd = "docker run --rm --memory={memory} --cpus={cpus} {image} {cmd}"
    val result = shell(full_cmd)
    if result.exit_code != 0:
        error("Container failed: {result.stderr}")
```

---

## Benefits of Conversion

### 1. Consistency
- ✅ All tools in one language
- ✅ Shared utilities (string, path, I/O)
- ✅ Unified error handling
- ✅ Common testing framework

### 2. Maintainability
- ✅ Type safety (catches errors at compile time)
- ✅ Better IDE support (LSP, autocomplete)
- ✅ Easier refactoring
- ✅ Self-documenting code (types show intent)

### 3. Portability
- ✅ Single binary (no bash/sh dependency)
- ✅ Cross-platform (Windows, FreeBSD, macOS)
- ✅ Consistent behavior across platforms
- ✅ No shell quoting issues

### 4. Integration
- ✅ Direct access to compiler internals
- ✅ Shared configuration (SDN format)
- ✅ Unified testing framework
- ✅ Better error messages

### 5. Self-hosting
- ✅ Eating our own dog food
- ✅ Validates Simple as a systems language
- ✅ Demonstrates real-world capabilities
- ✅ Increases confidence in the language

---

## Timeline

### Week 1-2 (Immediate)
- ✅ **filter_pending.spl** - Complete
- 🔄 **ci_runner.spl** - In progress
- 📝 **container_test.spl** - Planned
- 📝 **docker_runner.spl** - Planned

### Week 3-4 (Short-term)
- Build orchestration scripts (4-5 scripts)
- MCP testing scripts (2 scripts)

### Month 2 (Medium-term)
- Platform testing scripts (6 scripts)
- Cross-compilation scripts (2 scripts)

### Month 3+ (Long-term)
- Migration tools (6 scripts)
- Specialized tools (8+ scripts)

**Total estimated time:** 3-4 months at moderate pace (5-10 scripts/month)

---

## Success Metrics

### Quantitative
- Lines of shell code removed: ~5,700
- Lines of .spl code added: ~4,000 (30% reduction expected)
- Scripts converted: 32+
- Binary size impact: ~1MB for new apps (negligible)

### Qualitative
- Developer experience: Improved (IDE support, type safety)
- Bug rate: Reduced (compile-time checks)
- Platform coverage: Improved (Windows support)
- Documentation: Better (SDoctest examples)

---

## Next Steps

1. **Continue Phase 1:** Convert `ci-test.sh`, `local-container-test.sh`, `docker-test.sh`
2. **Test conversions:** Run converted scripts alongside originals to verify behavior
3. **Update CI:** Replace shell scripts with Simple equivalents gradually
4. **Document patterns:** Add conversion patterns to this document as we discover them
5. **Remove originals:** Delete `.sh` files after equivalents are verified

---

## Related Files

- **Conversion plan:** This file
- **API documentation:** `src/app/io/mod.spl` (exports list)
- **First conversion:** `src/app/test/filter_pending.spl`
- **Original scripts:** `script/` directory
- **Implementation report:** Will be created after each phase

---

## Notes

- Bootstrap scripts (3) must remain as shell - they run before Simple exists
- All other scripts can be converted to .spl or removed
- Simple I/O APIs are comprehensive - 99% of needed functionality exists
- Conversion typically results in 30% fewer lines (more expressive)
- Type safety and error handling add clarity without bloat

---

**Last updated:** 2026-02-15
**Status:** Phase 1 started, 1/32 scripts converted (3% complete)
**Next:** Convert ci-test.sh to ci_runner.spl
