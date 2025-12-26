# Driver Module Design

## Overview

The driver module orchestrates compilation, loading, and execution of Simple programs. This document defines the architecture for clean separation of concerns.

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                              src/driver/                                    │
│                                                                             │
│  ┌─────────────────┐     ┌─────────────────┐     ┌─────────────────┐       │
│  │   Interpreter   │────▶│     Runner      │────▶│    ExecCore     │       │
│  │  (High-level)   │     │   (Mid-level)   │     │   (Low-level)   │       │
│  └─────────────────┘     └─────────────────┘     └─────────────────┘       │
│          │                       │                       │                  │
│          │                       │                       ▼                  │
│          │                       │              ┌─────────────────┐        │
│          │                       │              │ CompilerPipeline │        │
│          │                       │              │  (src/compiler)  │        │
│          │                       │              └─────────────────┘        │
│          │                       │                       │                  │
│          │                       ▼                       ▼                  │
│          │              ┌─────────────────────────────────────────┐        │
│          │              │            SmfLoader                     │        │
│          │              │  load_from_file() / load_from_memory()  │        │
│          │              │           (src/loader)                   │        │
│          └──────────────┴─────────────────────────────────────────┘        │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Components

### 1. SmfLoader (src/loader) - ENHANCED

The SMF loader should support loading from both file and memory:

```rust
impl ModuleLoader {
    /// Load SMF from file path
    pub fn load(&self, path: &Path) -> Result<LoadedModule, LoadError>;

    /// Load SMF from file with custom symbol resolver
    pub fn load_with_resolver<F>(&self, path: &Path, resolver: F) -> Result<LoadedModule, LoadError>;

    /// NEW: Load SMF from memory buffer (for in-memory compilation)
    pub fn load_from_memory(&self, bytes: &[u8]) -> Result<LoadedModule, LoadError>;

    /// NEW: Load SMF from memory with custom symbol resolver
    pub fn load_from_memory_with_resolver<F>(&self, bytes: &[u8], resolver: F) -> Result<LoadedModule, LoadError>;
}
```

### 2. ExecCore (src/driver) - Low-level Execution Engine

Shared execution logic used by both Runner and Interpreter:

```rust
pub struct ExecCore {
    pub loader: SmfLoader,
    pub gc_alloc: Arc<dyn GcAllocator>,
    pub gc_runtime: Option<Arc<GcRuntime>>,
}

impl ExecCore {
    // Compilation
    pub fn compile_source(&self, source: &str, out: &Path) -> Result<(), String>;
    pub fn compile_file(&self, path: &Path, out: &Path) -> Result<(), String>;
    pub fn compile_to_memory(&self, source: &str) -> Result<Vec<u8>, String>;  // NEW

    // Loading
    pub fn load_module(&self, path: &Path) -> Result<LoadedModule, String>;
    pub fn load_module_from_memory(&self, bytes: &[u8]) -> Result<LoadedModule, String>;  // NEW

    // Execution
    pub fn run_smf(&self, path: &Path) -> Result<i32, String>;
    pub fn run_smf_from_memory(&self, bytes: &[u8]) -> Result<i32, String>;  // NEW

    // Combined (compile + load + run)
    pub fn run_source(&self, source: &str) -> Result<i32, String>;           // Uses temp file
    pub fn run_source_in_memory(&self, source: &str) -> Result<i32, String>; // NEW: No disk I/O
    pub fn run_file(&self, path: &Path) -> Result<i32, String>;              // Auto-detects .spl/.smf
}
```

### 3. Runner (src/driver) - Mid-level Public API

Simple API for compiling and running:

```rust
pub struct Runner {
    core: ExecCore,
}

impl Runner {
    // Constructors
    pub fn new() -> Self;
    pub fn new_no_gc() -> Self;
    pub fn with_gc_runtime(gc: GcRuntime) -> Self;

    // Run from source (compiles first)
    pub fn run_source(&self, source: &str) -> Result<i32, String>;

    // Run from file (auto-detects .spl or .smf)
    pub fn run_file(&self, path: &Path) -> Result<i32, String>;

    // Run pre-compiled SMF
    pub fn run_smf(&self, path: &Path) -> Result<i32, String>;

    // Compile only
    pub fn compile_to_smf(&self, source: &str, out: &Path) -> Result<(), String>;
    pub fn compile_to_memory(&self, source: &str) -> Result<Vec<u8>, String>;  // NEW
}
```

### 4. Interpreter (src/driver) - High-level API with I/O

Uses Runner internally, adds configuration and I/O capture:

```rust
pub struct Interpreter {
    runner: Runner,  // Changed from ExecCore to Runner
}

pub struct RunResult {
    pub exit_code: i32,
    pub stdout: String,
    pub stderr: String,
}

pub struct RunConfig {
    pub args: Vec<String>,
    pub stdin: String,
    pub timeout_ms: u64,
    pub in_memory: bool,  // NEW: If true, skip disk I/O
}

impl Interpreter {
    pub fn new() -> Self;
    pub fn new_no_gc() -> Self;

    /// Run with full configuration
    pub fn run(&self, code: &str, config: RunConfig) -> Result<RunResult, String>;

    /// Simple run (no config)
    pub fn run_simple(&self, code: &str) -> Result<RunResult, String>;

    /// Run in memory (no disk I/O) - NEW
    pub fn run_in_memory(&self, code: &str) -> Result<RunResult, String>;

    /// Access underlying runner for advanced use
    pub fn runner(&self) -> &Runner;
}
```

## Data Flow

### Mode 1: File-based (Current)

```
Source → compile_source() → temp.smf (disk) → load() → LoadedModule → run_main() → exit_code
```

### Mode 2: In-memory (New)

```
Source → compile_to_memory() → Vec<u8> → load_from_memory() → LoadedModule → run_main() → exit_code
```

## Implementation Plan

### Phase 1: Enhance SmfLoader (src/loader)

1. Add `load_from_memory(&[u8])` method
2. Add `load_from_memory_with_resolver(&[u8], F)` method
3. Refactor internal loading to share logic between file and memory paths

### Phase 2: Enhance CompilerPipeline (src/compiler)

1. Add `compile_to_memory(source: &str) -> Result<Vec<u8>, CompileError>`
2. Refactor `write_smf_with_return_value` to optionally return bytes instead of writing to file

### Phase 3: Update ExecCore (src/driver)

1. Add `compile_to_memory()` method
2. Add `load_module_from_memory()` method
3. Add `run_smf_from_memory()` method
4. Add `run_source_in_memory()` method

### Phase 4: Update Runner (src/driver)

1. Add `compile_to_memory()` public method
2. Add `run_in_memory()` public method (optional convenience)

### Phase 5: Update Interpreter (src/driver)

1. Change internal `core: ExecCore` to `runner: Runner`
2. Add `in_memory` flag to `RunConfig`
3. Add `run_in_memory()` convenience method
4. Delegate all execution to Runner

## Benefits

1. **No disk I/O for interpretation** - Faster execution when using in-memory mode
2. **Clear separation** - Interpreter uses Runner, Runner uses ExecCore
3. **Flexible loading** - SMF can come from file or memory
4. **Testability** - Can test loading without filesystem
5. **Embedding** - Easier to embed Simple in other applications

## File Changes Summary

| File | Changes |
|------|---------|
| `src/loader/src/loader.rs` | Add `load_from_memory()`, `load_from_memory_with_resolver()` |
| `src/compiler/src/pipeline.rs` | Add `compile_to_memory()`, refactor SMF writing |
| `src/driver/src/exec_core.rs` | Add memory-based methods |
| `src/driver/src/runner.rs` | Add `compile_to_memory()` |
| `src/driver/src/interpreter.rs` | Use Runner internally, add `run_in_memory()` |
