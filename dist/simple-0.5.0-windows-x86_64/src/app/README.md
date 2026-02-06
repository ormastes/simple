# Simple Self-Hosted Development Tools

Implementation of development tools for Simple language, written in Simple itself (dogfooding).

## Overview

All tools in this directory are:
- ✅ Written in Simple language (`.spl` files)
- ✅ Self-hosted (the language builds its own tools)
- ✅ Compiled to native binaries via `build_tools.sh`
- ✅ Zero external dependencies (except Simple stdlib)

**Tools:**
1. **Formatter** (`simple_fmt`) - ✅ Implemented
2. **Linter** (`simple_lint`) - ✅ Implemented
3. **Language Server** (`simple_lsp`) - 🔄 In Progress
4. **Debug Adapter** (`simple_dap`) - 🔄 In Progress
5. **Dependency Graph Generator** (`simple_depgraph`) - ✅ Implemented

## Structure

```
simple/
├── app/
│   ├── formatter/
│   │   └── main.spl          # Formatter implementation ✅
│   ├── lint/
│   │   └── main.spl          # Linter implementation ✅
│   ├── lsp/
│   │   ├── main.spl          # LSP server 🔄
│   │   ├── protocol.spl      # LSP protocol types 🔄
│   │   ├── transport.spl     # JSON-RPC transport 🔄
│   │   └── server.spl        # Server handlers 🔄
│   ├── dap/
│   │   ├── main.spl          # DAP server 🔄
│   │   ├── protocol.spl      # DAP protocol types 🔄
│   │   ├── transport.spl     # JSON-RPC transport 🔄
│   │   ├── server.spl        # Server handlers 🔄
│   │   └── breakpoints.spl   # Breakpoint management 🔄
│   └── depgraph/
│       ├── __init__.spl      # Module manifest ✅
│       ├── main.spl          # Entry point with AOP logging ✅
│       ├── scanner.spl       # Directory/file scanning ✅
│       ├── parser.spl        # Import extraction ✅
│       ├── analyzer.spl      # Dependency analysis ✅
│       └── generator.spl     # .__init__.spl generation ✅
├── bin_simple/               # Compiled executables
│   ├── simple_fmt           # Formatter binary ✅
│   ├── simple_lint          # Linter binary ✅
│   ├── simple_lsp           # LSP server binary 🔄
│   ├── simple_dap           # DAP server binary 🔄
│   └── simple_depgraph      # Depgraph binary ✅
├── build/                    # Intermediate build files
│   ├── formatter/           # Formatter .smf files
│   ├── lint/                # Linter .smf files
│   ├── lsp/                 # LSP .smf files 🔄
│   ├── dap/                 # DAP .smf files 🔄
│   └── depgraph/            # Depgraph .smf files ✅
└── build_tools.sh           # Build script for all tools
```

## Features

### Formatter (`simple_fmt`)

Canonical, zero-configuration formatter based on `doc/spec/formatting_lints.md`.

**Features:**
- ✅ Deterministic formatting (no configuration)
- ✅ 4-space indentation (always)
- ✅ Idempotent (format(format(x)) == format(x))
- ✅ Check mode (`--check`) for CI
- ✅ In-place formatting (`--write`)
- ⚠️ Basic line-by-line formatter (TODO: AST-based)

**Usage:**
```bash
# Print formatted output
./simple/bin_simple/simple_fmt file.spl

# Check if file is formatted (CI mode)
./simple/bin_simple/simple_fmt file.spl --check

# Format file in place
./simple/bin_simple/simple_fmt file.spl --write
```

### Linter (`simple_lint`)

Semantic linter with multiple lint categories based on `doc/spec/formatting_lints.md`.

**Lint Categories:**
- **Safety (S)**: Memory safety, null checks
- **Correctness (C)**: Logic errors, type mismatches
- **Warning (W)**: Potential issues, unused code
- **Style (ST)**: Naming conventions (allow by default)
- **Concurrency (CC)**: Thread safety issues

**Features:**
- ✅ Multiple lint levels (Allow/Warn/Deny)
- ✅ Fix-it hints in output
- ✅ Category-based organization
- ✅ Deny-all mode for strict checking
- ⚠️ Pattern-based linting (TODO: AST-based semantic analysis)

**Usage:**
```bash
# Run linter
./simple/bin_simple/simple_lint file.spl

# Treat warnings as errors
./simple/bin_simple/simple_lint file.spl --deny-all

# Enable all lints including style
./simple/bin_simple/simple_lint file.spl --warn-all
```

**Example Output:**
```
file.spl:10:0: warning[W001]: Unused variable (prefix with _ to silence)
  hint: Remove declaration or assign a value

file.spl:25:0: error[S001]: Unused Result type (must use .unwrap(), .expect(), or match)

Found 1 error(s) and 1 warning(s)
```

### Dependency Graph Generator (`simple_depgraph`)

Analyzes module dependencies and generates `.__init__.spl` (dot-prefixed) files with dependency information.

**Features:**
- ✅ Scans directories for .spl files and child modules
- ✅ Extracts imports (use, export use, common use)
- ✅ Identifies external dependencies (std.*, core.*, etc.)
- ✅ Enforces child module visibility rules
- ✅ AOP logging for all operations
- ✅ Recursive directory analysis
- ✅ Dry-run mode for preview

**Usage:**
```bash
# Analyze single directory
./simple/bin_simple/simple_depgraph ./src/mymodule

# Recursive analysis with verbose logging
./simple/bin_simple/simple_depgraph ./src --recursive --verbose

# Dry run (print without writing)
./simple/bin_simple/simple_depgraph ./src/api --dry-run --summary
```

**Options:**
| Option | Description |
|--------|-------------|
| `--recursive` | Analyze subdirectories recursively |
| `--verbose` | Enable verbose AOP logging |
| `--no-comments` | Omit comments from output |
| `--summary` | Print summary report |
| `--dry-run` | Print analysis without writing files |

**Example Output (`.__init__.spl`):**
```simple
# Auto-generated dependency analysis
# DO NOT EDIT - regenerate with: simple_depgraph ./src/mymodule

# External dependencies
# external: std.io
# external: core.json

# Child modules
pub mod api       # externally visible
mod internal      # BLOCKED: no export use

# Visibility Summary
# Externally visible: api
# Blocked (need export use): internal
```

**Child Visibility Rules:**
A child module's exports are blocked unless:
1. Parent's `__init__.spl` has `pub mod child`
2. Parent's `__init__.spl` has `export use child.symbol`

## Building

### Prerequisites

1. Simple compiler must be built:
   ```bash
   cargo build
   ```

2. Compiler should be available at `./simple/bin/simple`

### Build Tools

Run the build script:
```bash
./simple/build_tools.sh
```

This will compile all implemented tools:
1. Compile `formatter/main.spl` → `bin_simple/simple_fmt` ✅
2. Compile `lint/main.spl` → `bin_simple/simple_lint` ✅
3. Compile `lsp/main.spl` → `bin_simple/simple_lsp` 🔄 (when ready)
4. Compile `dap/main.spl` → `bin_simple/simple_dap` 🔄 (when ready)
5. Compile `depgraph/main.spl` → `bin_simple/simple_depgraph` ✅
6. Place intermediate files in `build/`

### Manual Build

If you need to build manually:
```bash
# Build formatter
./simple/bin/simple compile simple/app/formatter/main.spl \
    --output simple/bin_simple/simple_fmt \
    --build-dir simple/build/formatter

# Build linter
./simple/bin/simple compile simple/app/lint/main.spl \
    --output simple/bin_simple/simple_lint \
    --build-dir simple/build/lint
```

## Implementation Status

### Formatter

| Feature | Status | Notes |
|---------|--------|-------|
| Basic indentation | ✅ | 4-space indent |
| Line-by-line formatting | ✅ | Simple implementation |
| Check mode | ✅ | Exit 1 if not formatted |
| Write mode | ✅ | Format in place |
| AST-based formatting | ⚠️ TODO | Requires parser integration |
| Comment preservation | ⚠️ TODO | Requires parser |
| Max line length | ⚠️ TODO | Requires smart wrapping |

### Linter

| Feature | Status | Notes |
|---------|--------|-------|
| Safety lints | ✅ | Basic pattern matching |
| Correctness lints | ✅ | Basic pattern matching |
| Warning lints | ✅ | Unused variables |
| Style lints | ✅ | Naming conventions |
| Concurrency lints | ⚠️ Partial | Needs semantic analysis |
| Fix-it hints | ✅ | Text suggestions |
| AST-based analysis | ⚠️ TODO | Requires compiler integration |
| Control flow analysis | ⚠️ TODO | Requires compiler integration |

## Language Server (`simple_lsp`) - 🔄 In Progress

**Status:** Reimplementing in Simple (was Rust prototype at `src/lsp/`)

Self-hosted LSP server for editor integration (VS Code, Neovim, etc.).

**Planned Features:**
- ⏳ JSON-RPC 2.0 transport over stdio
- ⏳ Document synchronization (didOpen, didChange)
- ⏳ Real-time diagnostics (parse errors, type errors)
- ⏳ Code completion (context-aware)
- ⏳ Go to definition
- ⏳ Hover documentation
- ⏳ Find references
- ⏳ Syntax highlighting (semantic tokens)

**Usage (when complete):**
```bash
# Start LSP server (communicates via stdin/stdout)
./simple/bin_simple/simple_lsp

# VS Code: Configure in settings.json
# Neovim: Configure with nvim-lspconfig
```

**See:** `doc/status/lsp_implementation.md` for detailed status

---

## Debug Adapter (`simple_dap`) - 🔄 In Progress

**Status:** Reimplementing in Simple (was Rust prototype at `src/dap/`)

Self-hosted DAP server for debugging Simple programs.

**Planned Features:**
- ⏳ DAP protocol over stdio
- ⏳ Breakpoint management (line, conditional, function)
- ⏳ Execution control (continue, step over, step in, step out)
- ⏳ Stack trace inspection
- ⏳ Variable viewing and evaluation
- ⏳ Watch expressions
- ⏳ Exception breakpoints
- ⏳ Interpreter integration (actual debugging)

**Usage (when complete):**
```bash
# Start DAP server
./simple/bin_simple/simple_dap

# VS Code: Configure launch.json
# Neovim: Use nvim-dap
```

**See:** `doc/status/dap_implementation.md` for detailed status

---

## Roadmap

### Phase 1: Formatter & Linter (Done)
- ✅ Line-by-line formatter
- ✅ Pattern-based linter
- ✅ Command-line interface
- ✅ Build infrastructure

### Phase 2: Essential Utilities (Planned)
- ⏳ `simple_doc` - Generate markdown from docstrings
- ⏳ `simple_todo` - Extract TODO/FIXME comments
- ⏳ `simple_stats` - Code statistics (LOC, functions, classes)
- ⏳ `simple_new` - Project scaffolding

### Phase 3: Quality Tools (Planned)
- ⏳ `simple_test` - BDD test runner with nice output
- ⏳ `simple_grep` - AST-aware code search
- ⏳ `simple_deps` - Import dependency graph
- ⏳ `simple_dead` - Dead code detector

### Phase 4: LSP & DAP Implementation (In Progress)
- 🔄 LSP: JSON-RPC transport
- 🔄 LSP: Document sync and diagnostics
- 🔄 DAP: Protocol handling
- 🔄 DAP: Breakpoint management

### Phase 5: Advanced Tools (Future)
- ⏳ `simple_repl` - Interactive shell
- ⏳ `simple_bench` - Benchmark runner
- ⏳ `simple_cov` - Code coverage
- ⏳ `simple_refactor` - Rename/extract/inline
- ⏳ `simple_security` - SAST scanner

## Tool Specifications

See `spec/` directory for detailed specifications.

## Testing

Create a test file:

```simple
# test.spl
fn  example( ):
let x=1
if x>0:
print("hello")
```

Format it:
```bash
./simple/bin_simple/simple_fmt test.spl --write
```

Result:
```simple
# test.spl
fn example():
    let x = 1
    if x > 0:
        print("hello")
```

Lint it:
```bash
./simple/bin_simple/simple_lint test.spl
```

## Contributing

When implementing new lints or formatting rules:

1. Update `doc/spec/formatting_lints.md` with specification
2. Add feature to `doc/features/feature.md`
3. Implement in `simple/app/formatter/` or `simple/app/lint/`
4. Add tests
5. Update this README

## References

- **Formatter/Linter Spec**: `doc/spec/formatting_lints.md`
- **LSP Status**: `doc/status/lsp_implementation.md`
- **DAP Status**: `doc/status/dap_implementation.md`
- **Features**:
  - Formatter/Linter: `doc/features/feature.md` (#1131-#1145)
  - LSP: `doc/features/postponed_feature.md` (#1359-#1365)
  - DAP: `doc/features/postponed_feature.md` (#1366-#1368)
- **Examples**: `simple/test/` directory

## Why Self-Hosted?

Writing Simple's development tools in Simple itself provides:

1. **Dogfooding**: We use our own language daily, finding bugs and UX issues
2. **Proof of Capability**: Shows Simple can build real-world tools
3. **Performance Testing**: Exercises the compiler on substantial codebases
4. **Community Example**: Demonstrates best practices for Simple development
5. **Zero Dependencies**: No Rust/Python/etc needed for tooling once bootstrapped
