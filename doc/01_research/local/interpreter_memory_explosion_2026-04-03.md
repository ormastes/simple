# Research: Interpreter Memory Explosion in MCP Servers

**Date:** 2026-04-03
**Status:** ALL BUGS FIXED (BUG-1/2/3/4/5/6/7)
**Severity:** Critical — T32 MCP servers OOM-killed at 100MB watchdog limit

## Fix Results — All Stages

### Stage 1: Arc<Env> only (BUG-1)
| Workload | Before (MB) | After (MB) | Reduction |
|----------|------------|-----------|-----------|
| T32 LSP MCP main.spl | 132 | 57 | -57% |
| CMM daemon (narrow lib) | 8,923 | 305 | -97% |
| `use std.io.{print}` | 7,270 | 72 | -99% |

### Stage 2: Arc<Env> + No Cascade Merge (BUG-1 + BUG-4/7)
| Workload | Before (MB) | After (MB) | Reduction |
|----------|------------|-----------|-----------|
| Baseline (`--version`) | 14 | 14 | same |
| T32 MCP cold (no imports) | 29 | 25 | -14% |
| T32 LSP MCP main.spl | 132 | **31** | **-76%** |
| CMM daemon (narrow lib) | 8,923 | **76** | **-99.1%** |
| `use std.io.{print}` | 7,270 | **21** | **-99.7%** |

### Stage 3: Arc<FunctionDef> + Sibling Preload Cap (BUG-5 + BUG-3)
| Workload | Before (MB) | After (MB) | Reduction |
|----------|------------|-----------|-----------|
| Baseline (`--version`) | 14 | 14 | same |
| T32 LSP MCP main.spl | 132 | **27** | **-80%** |
| CMM daemon (narrow lib) | 8,923 | **57** | **-99.4%** |
| `use std.io.{print}` | 7,270 | **21** | **-99.7%** |

**ALL T32 MCP servers fit under 100MB watchdog. Zero crash logs. 112,384 tests passed.**

## Problem Statement

T32 MCP and T32 LSP MCP servers crash during loading because the Simple interpreter
uses far more memory than expected. A program with zero imports should stay under 30MB,
yet moderate imports push RSS to 130MB+ and the CMM LSP daemon reaches 8-10GB.

## Measured RSS Baselines

| Workload | SIMPLE_LIB | RSS (MB) | Expected |
|----------|-----------|----------|----------|
| `bin/simple --version` | n/a | 14 | OK |
| `print "hello"` (zero imports) | none | 18 | OK |
| T32 MCP cold frontend (zero imports) | src | 29 | OK |
| T32 LSP MCP main.spl (3 imports) | src | 132 | **BAD** |
| `use std.io.{print}` (1 import) | src | 7,270 | **CRITICAL** |
| CMM LSP mcp_daemon.spl (6 imports) | cmm_lsp | 8,923 | **CRITICAL** |
| CMM LSP mcp_daemon.spl (6 imports) | src | 10,384 | **CRITICAL** |
| Precompiled native t32_mcp | n/a | 2.8 | OK |

## Root Causes Identified

### BUG-1: Per-Function Environment Deep Clone (O(N*M) memory)

**Location:** `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs:555-601`

The `export_functions()` function clones the entire `filtered_env` HashMap into every
exported function's `captured_env` field:

```rust
for (name, f) in local_functions {
    let func_with_env = Value::Function {
        name: name.clone(),
        def: Box::new(f.clone()),
        captured_env: filtered_env.clone(),  // FULL DEEP CLONE per function
    };
    env.insert(name.clone(), func_with_env.clone());  // ANOTHER deep clone
    exports.insert(name.clone(), func_with_env);
}
```

For a module with N functions and an environment of M entries, this creates 2N
independent deep copies of the entire environment. The `Value` enum is a 35+ variant
type with heap-allocated String, HashMap, Vec, and Box<FunctionDef>.

**Impact:** A module with 30 functions and 50-symbol environment creates 60 deep copies
of the environment. With nested Value::Dict values, this easily reaches tens of MB per module.

**Fix:** Change `Value::Function.captured_env` from `Env` (HashMap) to `Arc<Env>`.
Create one Arc per module, share it across all functions. O(N*M) -> O(M) memory.

### BUG-2: SIMPLE_LIB Misconfiguration for LSP Daemon

**Location:** `bin/release/t32_lsp_mcp_server:45-58`

The wrapper sets `SIMPLE_LIB=${REPO_ROOT}/src` but the daemon subprocess
(`cmm_lsp/mcp_daemon.spl`) imports `t32_lsp_mcp.json_helpers` which lives under
`examples/10_tooling/trace32_tools/t32_lsp_mcp/`. With `SIMPLE_LIB=src`, the resolver:
1. Fails to find `t32_lsp_mcp` under `src/`
2. Walks up parent directories scanning each one
3. Triggers stdlib directory scanning (4,553 files under src/)
4. Sibling preloading kicks in for `__init__.spl` files, loading entire packages

**Impact:** +1.5GB RSS just from the SIMPLE_LIB misconfiguration (8.9GB narrow vs 10.4GB wide).

**Fix:** Set `SIMPLE_LIB` to `examples/10_tooling/trace32_tools` for the daemon subprocess,
matching how the t32_mcp_server wrapper handles `FULL_SIMPLE_LIB`.

### BUG-3: Unbounded Sibling Preloading in __init__.spl

**Location:** `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:505-628`

When loading an `__init__.spl` with bare exports, the loader reads ALL sibling `.spl`
files in the directory, parses them, and evaluates their exports. The name-matching
check (`sibling_might_define_requested_names`, line 75) does a full `fs::read_to_string`
on each candidate file.

For stdlib directories under `src/lib/` (which have many `__init__.spl` files), this
cascades: loading one `__init__.spl` triggers sibling preloading, which imports other
modules with their own `__init__.spl` files, triggering more sibling preloading.

**Impact:** `use std.io.{print}` with `SIMPLE_LIB=src` costs 7.1GB because it touches
the entire `src/lib/` tree (20+ MB of source, ~1,100x memory amplification from
AST representation + environment cloning).

**Fix:** Add a total-bytes or total-files cap on sibling preloading. Skip preloading
when the resolved module is outside the project's declared source roots.

### BUG-4: Cascading Environment Growth Across Import Chain

**Location:** `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:647-688`

When module A imports module B which imports module C, environments cascade. Each
import level merges its environment ON TOP of child module's captured environments.
Environments grow cumulatively: functions from D carry envs from D+C+B+A.

**Impact:** Quadratic growth with import chain depth. Deep import chains like
`mcp_daemon -> cmm_parser_runtime -> cmm_tokens + cmm_ast + cmm_lexer + cmm_parser_core`
cause environment sizes to snowball.

**Fix:** Resolved by BUG-1 fix (Arc sharing eliminates the cascade cost).

### BUG-7: Module Loader Cascade Merge Defeats Arc Sharing

**Location:** `src/compiler_rust/compiler/src/interpreter_module/module_loader.rs:647-688` (before fix)

Even after BUG-1 Arc fix, the module loader deep-cloned each function's `captured_env`
back out of the Arc (`HashMap::clone(&existing_env)`) and merged the importing module's
`filtered_env` on top. This created a NEW HashMap per re-exported function, defeating
the Arc sharing entirely at module boundaries.

**Impact:** Functions carried cascading environments from every module in the import chain.
For a 6-deep import chain with 170 total functions, this was the primary remaining cause
of the 305MB peak after BUG-1 fix.

**Fix:** Removed the cascade merge entirely. Functions keep their original `captured_env`
from their defining module. The importer's variables are irrelevant to the imported
function's execution — functions already have everything they need from their own module.
Result: 305MB -> 76MB for the CMM daemon.

### BUG-5: Module Cache Stores Full Clones (No Structural Sharing)

**Location:** `src/compiler_rust/compiler/src/module_cache.rs:57-75`

The module cache uses 7 separate thread-local HashMaps, all storing full clones.
Every `FunctionDef` AST node exists in at least 3 places:
1. `MODULE_FUNCTIONS_CACHE`
2. Inside `Value::Function` in `MODULE_EXPORTS_CACHE`
3. In the caller's local `functions` HashMap

No `Arc`-based sharing of AST structures.

**Fix:** Use `Arc<FunctionDef>` instead of `Box<FunctionDef>` in `Value::Function`.

### BUG-6: stderr Silenced in Production Wrappers

**Location:** `bin/release/t32_mcp_server:221-243`, `bin/release/t32_lsp_mcp_server:62-67`

Both wrappers redirect `2>/dev/null` when debug mode is off (the default). All error
output including OOM crash messages, module resolution errors, and runtime panics are
completely invisible.

**Fix:** Redirect stderr to `.simple/logs/t32_mcp_stderr.log` and
`.simple/logs/t32_lsp_mcp_stderr.log` instead of `/dev/null`.
(Already applied in this session.)

## Prevention Strategy

### 1. Memory Budget Tracking in Interpreter

Add RSS tracking at module load boundaries:
```
[module-load] path=t32_mcp/session_tools.spl rss_before=45MB rss_after=67MB delta=+22MB
```
This makes memory regressions immediately visible in logs.

### 2. Structural Sharing by Default

All large AST/Value structures should use `Arc<T>` not `Box<T>` or raw clones.
The interpreter's memory model should be copy-on-write, not copy-always.

### 3. Module Loading Budget

Add configurable limits:
- `SIMPLE_MODULE_LIMIT`: max number of modules loaded (default: 100)
- `SIMPLE_SIBLING_PRELOAD_LIMIT`: max files per __init__.spl preload (default: 20)
- `SIMPLE_MODULE_RSS_WARN_MB`: warn when a single module load adds >N MB

### 4. SIMPLE_LIB Scope Validation

When `SIMPLE_LIB` points at a directory with >1000 files, log a warning.
MCP wrappers should always set the narrowest possible `SIMPLE_LIB`.

### 5. CI Memory Regression Gate

Add a CI job that runs key MCP entry points with `SIMPLE_MEMORY_LIMIT_MB=100`
and asserts they load successfully. Any regression fails the build.

### 6. Arc-by-Default Policy for AST/Value Types

All large heap types in the interpreter should use `Arc<T>` not `Box<T>` or raw clones:
- `FunctionDef` — **Done** (Arc in Value, cache, and exports pipeline)
- `ClassDef` — Next candidate (same cache pattern)
- `EnumDef` — Next candidate
- `Env` (captured_env) — **Done** (Arc)

**Rule:** If a type appears in both a cache and a Value variant, it MUST be `Arc<T>`.
If it's cloned more than once during module loading, it MUST be `Arc<T>`.

### 7. Module Loading Memory Budget (Future)

Add per-module RSS delta tracking:
```
[module-load] path=cmm_parser_runtime.spl rss_before=16MB rss_after=18MB delta=+2MB functions=3
```
When delta exceeds a configurable threshold (e.g., 10MB), emit a warning.
This makes memory regressions visible immediately in development.

### 8. SIMPLE_LIB Scope Validation

When `SIMPLE_LIB` points at a directory with >500 `.spl` files, emit a warning:
```
[warn] SIMPLE_LIB=/path/to/src contains 4553 .spl files — consider narrowing scope
```
MCP wrappers should always set the narrowest possible `SIMPLE_LIB`.

## Fix Priority

| Bug | Impact | Effort | Priority | Status |
|-----|--------|--------|----------|--------|
| BUG-6 (stderr logging) | Observability | Low | P0 | **DONE** |
| BUG-2 (SIMPLE_LIB daemon) | -1.5GB RSS | Low | P0 | **DONE** |
| BUG-1 (Arc<Env> captured_env) | -50-90% RSS | Medium | P0 | **DONE** |
| BUG-7 (cascade merge defeat Arc) | -75% RSS after BUG-1 | Low | P0 | **DONE** |
| BUG-4 (cascade env growth) | Fixed by BUG-1+7 | None | N/A | **DONE** |
| BUG-5 (Arc<FunctionDef>) | -25% RSS after BUG-1 | Medium | P1 | **DONE** |
| BUG-3 (sibling preload cap) | Prevents edge cases | Low | P1 | **DONE** |

**Verification:** 112,384 tests passed, 0 failed. All MCP servers under 100MB watchdog.
