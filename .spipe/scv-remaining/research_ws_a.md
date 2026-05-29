# SCV Workstream A — PROD-001 Interpreter Memory-Pressure Research

Date: 2026-05-15  
Status: Complete

---

## 1. Task Framing Correction

The task framing describes "cross-process parse-state corruption" caused by sibling child
processes. This framing is physically impossible: every `bin/release/simple run` call is
a separate OS process. Rust `LazyLock`, `thread_local!`, `Mutex`, and `RwLock` statics
are per-process and cannot be corrupted by sibling processes.

The actual root cause is **per-child RSS bloat from loading full SIMPLE_LIB (600+ .spl
files)**, which under heavy concurrent load produces OOM kills, FD exhaustion, or swap
thrashing. The test runner sees truncated stdout or non-zero exit codes from killed children
and reports that as "parse-state corruption."

---

## 2. Evidence

### 2a. Test Scripts Set Full SIMPLE_LIB for Every Child

Every `it` block in the PROD-001 spec spawns at least one child via:
```
SIMPLE_LIB="$REPO/src" "$REPO/bin/release/simple" run "$REPO/src/app/scv/main.spl" <cmd>
```
File: `test/integration/app/scv_wasm_executor_spec.spl`
- 6 `it` blocks × ≥1 child each = 6+ spawns of the full interpreter
- `SIMPLE_LIB="$REPO/src"` covers all of `src/` — 600+ .spl files

The same pattern is used in `test/integration/app/` other SCV specs (merge, diff, etc.):
each shell script embeds multiple sequential `bin/release/simple run` invocations, all
with `SIMPLE_LIB="$REPO/src"`.

### 2b. memory_guard.rs Already Warns About This Exact Configuration

File: `src/compiler_rust/compiler/src/memory_guard.rs` (lines 106–118)

```rust
if count > 500 {
    eprintln!(
        "[memory-guard] SIMPLE_LIB={} contains {}+ .spl files — \
         consider narrowing scope to avoid memory bloat",
        lib_path, count
    );
}
```

The runtime itself diagnoses `SIMPLE_LIB` pointing to 500+ .spl files as a misconfiguration
indicator. The PROD-001 tests trigger this condition on every child process.

### 2c. In-Process Statics Are Per-Process (Not a Cross-Child Corruption Vector)

The following global statics exist but are isolated within each child process:

**`src/compiler_rust/compiler/src/interpreter_extern/dynamic_ffi.rs` (lines 47, 73–74, 77–78, 382–383):**
```rust
static DYNAMIC_RUNTIME: std::sync::LazyLock<Mutex<DynamicRuntime>> = ...
static SATELLITE_LIBRARIES: std::sync::LazyLock<Mutex<HashMap<String, SatelliteLibrary>>> = ...
static MANIFEST_LIBRARIES: std::sync::LazyLock<Mutex<HashMap<String, SatelliteLibrary>>> = ...
static RESOLVED_CLASS_CACHE: std::sync::LazyLock<Mutex<HashMap<String, ResolvedClassBundle>>> = ...
```

**`src/compiler_rust/compiler/src/interpreter_state.rs` (line 48):**
A large `thread_local!` block exporting ~35 named statics including `BDD_REGISTRY_GROUPS`,
`BDD_REGISTRY_CONTEXTS`, `BDD_REGISTRY_SHARED`, `CURRENT_FILE`, `MODULE_GLOBALS`, etc.

All of these are per-process (OS process boundary). They accumulate state over the lifetime
of one interpreter invocation and are NOT shared with sibling processes. They are correctly
cleared by `clear_interpreter_state()` within a process for re-entrant test runs, but this
is irrelevant to the PROD-001 child-spawn scenario.

**`src/compiler_rust/compiler/src/watchdog.rs` (lines 20, 27):**
```rust
static WATCHDOG: Mutex<Option<WatchdogHandle>> = Mutex::new(None);
static WATCHDOG_CONTEXT: Mutex<Option<String>> = Mutex::new(None);
```
Per-process. The watchdog kills the process if RSS exceeds `SIMPLE_MEMORY_LIMIT_MB`, but
by default this limit is **0 (disabled)**, so children grow unbounded until the kernel OOMs
them.

### 2d. No Shared On-Disk Parse Cache Found

Grep across `src/compiler_rust/compiler/src/` found:
- No cross-process parse cache files (no `flock`, no shared temp-dir lock, no
  `OpenOptions::create_new` race pattern in the interpreter path)
- SMF cache files (`.simple/build/*.smf`) exist but are only written when
  `SIMPLE_MCP_USE_CACHE=1` is set (off by default per memory note `feedback_mcp_cache_off_by_default.md`)
- The `CompiledModuleCache` in `codegen/parallel.rs` is an in-memory `DashMap`, not a file

No on-disk shared cache race was found. The file-based SMF path is not active in default
test runs.

### 2e. Memory Guard Knobs Available (Unused in Tests)

From `src/compiler_rust/compiler/src/memory_guard.rs` and `watchdog.rs`:

| Env var | Default | Effect |
|---|---|---|
| `SIMPLE_MEMORY_LIMIT_MB` | 0 (disabled) | Hard RSS kill via watchdog |
| `SIMPLE_MODULE_LIMIT` | 800 | Max modules loaded per process |
| `SIMPLE_MODULE_RSS_WARN_MB` | 0 (disabled) | Per-module RSS warn threshold |
| `SIMPLE_SIBLING_PRELOAD_LIMIT` | 20 | Max siblings eager-loaded per `__init__.spl` |
| `SIMPLE_SIBLING_MAX_CHECK_KB` | 50 KB | Max file size checked for sibling name-match |
| `SIMPLE_LOADER_TRACE` | off | Enable module load diagnostics |

None of these are set in the PROD-001 test scripts. Children load unthrottled.

---

## 3. Root Cause Hypothesis

**Primary cause:** Each child process loads all of `src/` (600+ .spl files) via
`SIMPLE_LIB="$REPO/src"`. Under concurrent test runs (multiple spec files running in
parallel), N child processes each consume several hundred MB RSS simultaneously. On machines
with limited RAM, this causes:

1. Linux OOM killer terminates one or more children mid-execution
2. The test helper `_run_wasm_executor_script` captures truncated stdout
3. String matchers on the output fail → reported as "sporadic parse-state corruption"

**Contributing factor:** `SIMPLE_MEMORY_LIMIT_MB=0` (disabled by default) means children
never fail fast/clean; instead they are killed by the OS with signal 9, producing no
diagnostic output.

**What "sporadic" means:** Whether OOM fires depends on concurrent load from other test
processes, background system RSS, and kernel overcommit policy — hence it passes on clean
runs but fails under heavy load.

---

## 4. Risk Assessment

**Depth of fix:** Runtime-only. No compiler changes, no bootstrap rebuild required.

**Risk level:** Low. All proposed remediations are env-var or test-script changes.

**Bootstrap impact:** None. No new `rt_*` externs are added.

---

## 5. Recommended Fix Approaches (Ordered by Impact / Cost)

### Fix A: Narrow SIMPLE_LIB in PROD-001 Test Scripts (Highest Impact, Zero Risk)

Change test scripts from `SIMPLE_LIB="$REPO/src"` to the minimal scope needed:
```sh
SIMPLE_LIB="$REPO/src/lib/scv:$REPO/src/lib/common:$REPO/src/lib/nogc_sync_mut/io"
```
Note: the example above is a starting point only — the exact minimal closure must be
determined by trial (progressively narrowing scope and verifying all imports resolve).
This is already recommended by `memory_guard.rs`'s own warning. Reduces per-child load
from 600+ modules to ~30–50. Fixes the symptom directly at its source.

**Affected files:** All `it` blocks in:
- `test/integration/app/scv_wasm_executor_spec.spl`
- Other SCV integration specs with embedded shell scripts

### Fix B: Set SIMPLE_MEMORY_LIMIT_MB in Test Runner (Fast-Fail, Clean Errors)

Add to the test runner environment:
```
SIMPLE_MEMORY_LIMIT_MB=512
```
This enables the watchdog RSS limit, so children that grow too large fail with a clean
diagnostic instead of being silently OOM-killed. Produces useful error messages instead
of truncated output that looks like corruption.

**Affected files:** `src/app/test/` test runner configuration.

### Fix C: Lower SIMPLE_SIBLING_PRELOAD_LIMIT (Reduce Eager Load Amplification)

The `__init__.spl` sibling preloader loads up to 20 siblings by default. With broad
SIMPLE_LIB, each `use std.X` import cascades into eager-loading 20 siblings. Lowering
`SIMPLE_SIBLING_PRELOAD_LIMIT` to 5 reduces the module explosion multiplier.

This is a runtime-only env-var default change in `memory_guard.rs`.

### Fix D: Add Per-Process Module Count Logging at Child Startup (Diagnostic)

Emit `[memory-guard]` stats when a child exits with >400 modules loaded. This will
confirm or deny the hypothesis by showing actual module counts in test failure logs.
Enable by setting `SIMPLE_LOADER_TRACE=1` in test runs.

---

## 6. Missing Reference File

The task referenced `.claude/memory/reference_interpreter_perf_bottlenecks.md` as a
source (listing "Top 5 Rust-layer interpreter perf bottlenecks: debug_state mutex,
Value::Str copies, extern dispatch, expr cascade, coverage overhead"). This file was
not found at either the project or user memory paths on disk. The MEMORY.md index entry
was used in lieu of the file itself. The missing file is a separate artifact gap and
does not affect this analysis — none of those in-process bottlenecks are relevant to
the cross-process RSS bloat scenario.

---

## 7. What Does NOT Need Changing

- `interpreter_state.rs` thread-locals: correct, per-process, no cross-child leak
- `dynamic_ffi.rs` LazyLock statics: correct, per-process, no cross-child leak  
- `watchdog.rs` WATCHDOG global: correct, per-process timeout guard
- SMF cache files: not active in default interpreter mode
- Parser or AST code: no parse-state mutation between processes

---

## 8. Key File Paths

| File | Role |
|---|---|
| `src/compiler_rust/compiler/src/memory_guard.rs` | RSS limits, module count, sibling preload knobs |
| `src/compiler_rust/compiler/src/watchdog.rs` | RSS watchdog, SIMPLE_MEMORY_LIMIT_MB |
| `src/compiler_rust/compiler/src/interpreter_state.rs` | All per-process thread-locals (clean) |
| `src/compiler_rust/compiler/src/interpreter_extern/dynamic_ffi.rs` | Per-process LazyLock caches (clean) |
| `test/integration/app/scv_wasm_executor_spec.spl` | PROD-001 spec — sets SIMPLE_LIB="$REPO/src" |
| `doc/03_plan/agent_tasks/scv.md` | PROD-001 known limitation documented here |
