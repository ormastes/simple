# Simple Language - Project Structure Guide

**Quick Navigation:** Where to find what you're looking for

**Last Updated:** 2026-02-16
**For detailed analysis:** See [doc/architecture/file_class_structure.md](../../architecture/file_class_structure.md)

---

## Root Directory Overview

```
simple/
├── Essential Files (5 files)
├── Source Code (src/)
├── Tests (test/)
├── Documentation (doc/)
├── Configuration (config/)
├── Scripts & Tools (scripts/, tools/)
├── Build & Distribution (bin/, build/, dist/)
└── Supporting Files (tools/, examples/, config/, etc.)
```

---

## Root Files (Essential Only)

### **Project Documentation**

| File | Purpose | Read When |
|------|---------|-----------|
| `README.md` | Main project introduction, quick start | First time visiting |
| `CLAUDE.md` | Development guide, coding standards | Contributing code |
| `AGENTS.md` | Agent definitions -> redirects to CLAUDE.md | Looking for agents |
| `CHANGELOG.md` | Version history, what's new | Before upgrading |

### **Project Configuration**

| File | Purpose | Edit When |
|------|---------|-----------|
| `simple.sdn` | Main project config (solution-wide) | Changing project structure |
| `VERSION` | Current version number (0.6.1) | Releasing new version |

### **Hidden Files (Don't Edit)**

| File | Purpose |
|------|---------|
| `.gitignore` | Git exclusion patterns |
| `.jjignore` | Jujutsu VCS exclusion patterns |
| `.dockerignore` | Docker build exclusions |
| `.mcp.json` | MCP server configuration |
| `.envrc` | Direnv environment setup |

---

## Main Directories

### **Source Code: `src/`** (111,044 lines, production code)

```
src/
├── compiler/       # Unified compiler -- numbered layers
│   ├── 00.common/      # Error types, config, effects, visibility, diagnostics, registry
│   ├── 10.frontend/    # Lexer, parser, AST, treesitter, desugar, parser types
│   ├── 15.blocks/      # Block definition system
│   ├── 20.hir/         # HIR types, definitions, lowering, inference
│   ├── 25.traits/      # Trait def, impl, solver, coherence, validation
│   ├── 30.types/       # Type inference, type system, dimension constraints
│   ├── 35.semantics/   # Semantic analysis, lint, macro check, resolve, const eval
│   ├── 40.mono/        # Monomorphization, instantiation
│   ├── 50.mir/         # MIR types, data, instructions, lowering, serialization
│   ├── 55.borrow/      # Borrow checking, GC analysis
│   ├── 60.mir_opt/     # MIR optimization passes
│   ├── 70.backend/     # Backends (LLVM, C, Cranelift, WASM, CUDA, Vulkan, Native), linker
│   ├── 80.driver/      # Driver, pipeline, project, build mode, incremental
│   ├── 85.mdsoc/       # MDSOC (virtual capsules, feature, transform, weaving, adapters)
│   ├── 90.tools/       # API surface, coverage, query, symbol analyzer, AOP
│   ├── 95.interp/      # Interpreter, MIR interpreter, execution
│   └── 99.loader/      # Module resolver, loader
│
├── lib/            # Standard library -- `use std.X` resolves here
│   ├── common/         # Pure functions, no mutation (text, math, json, crypto, encoding)
│   ├── nogc_sync_mut/  # Sync mutable, no GC (ffi, fs, net, http, database, mcp, spec)
│   ├── nogc_async_mut/ # Async mutable, no GC (actors, async, threads, generators)
│   ├── gc_async_mut/   # GC + async (gpu, cuda, torch, pure ML library)
│   └── nogc_async_mut_noalloc/  # Baremetal, execution, memory, qemu
│
├── app/            # Applications & tools
│   ├── cli/            # Command-line interface
│   ├── build/          # Build system
│   ├── test_runner_new/ # Test runner
│   ├── mcp/            # MCP servers (file I/O, debug)
│   ├── mcp_jj/         # Jujutsu VCS MCP
│   ├── io/             # I/O subsystem
│   └── desugar/        # Code transformations
│
├── runtime/        # C runtime (runtime.c/runtime.h -- linked by generated C++)
├── compiler_cpp/   # Generated C from Simple source (temporal bootstrap)
└── i18n/           # Internationalization
```

**Go here when:**
- Writing new features -> `src/lib/` or `src/app/`
- Fixing compiler bugs -> `src/compiler/`
- Adding ML features -> `src/lib/gc_async_mut/`
- Building tools -> `src/app/`

---

### **Tests: `test/`**

```
test/
├── unit/           # Unit tests (most tests here)
│   ├── std/            # Standard library tests
│   ├── app/            # Application tests
│   └── compiler/       # Compiler tests
│
├── integration/    # Integration tests
├── system/         # System/end-to-end tests
├── benchmarks/     # Performance benchmarks (executable, not test specs)
└── lib/            # Test utilities & symlinks
```

**Go here when:**
- Writing tests for new features -> `test/unit/`
- Testing integration -> `test/integration/`
- End-to-end testing -> `test/system/`
- Measuring performance -> `test/benchmarks/`

---

### **Documentation: `doc/`**

```
doc/
├── Status Reports
│   ├── EXECUTIVE_SUMMARY.md
│   ├── production_readiness.md
│   └── features_that_work.md
│
├── User Guides (guide/)
│   ├── quick_reference/    # Quick reference guides
│   ├── writing/            # Writing guides (application, design, architecture)
│   ├── backend/            # Compiler backend guides
│   └── ...                 # Other topic guides
│
├── Architecture (architecture/)
│   ├── overview.md
│   ├── file_class_structure.md
│   └── architecture.md
│
├── Technical (design/, research/, plan/)
│
└── Generated (feature/, test/, bug/)
    ├── feature/feature.md
    ├── test/test_result.md
    └── bug/bug_report.md
```

**Go here when:**
- Learning the language -> `doc/guide/`
- Understanding architecture -> `doc/architecture/`
- Checking status -> Root `doc/*.md` files
- Planning features -> `doc/design/`, `doc/plan/`

---

### **Configuration: `config/`**

| File | Purpose | Used By |
|------|---------|---------|
| `bootstrap.sdn` | Bootstrap build settings | Build system |
| `dl.config.sdn` | Deep learning GPU config | ML/DL code |
| `doc_coverage.sdn` | Doc coverage thresholds | Documentation tools |
| `docker-compose.yml` | Main Docker environment | Development |
| `docker-compose.test.yml` | Test isolation | CI/CD |
| `sdoctest.sdn` | Documentation testing | Test runner |
| `simple.intensive.sdn` | Intensive test config | Heavy testing |
| `simple.test.sdn` | Test suite config | Test runner |

---

### **Binaries: `bin/`**

```
bin/
├── simple              # Current build (debug)
└── release/
    └── simple          # Pre-built runtime (production)
```

- `bin/simple` - Run Simple commands
- `bin/release/simple` - Stable pre-built version (fully self-sufficient)

---

### **Other Directories**

| Directory | Purpose |
|-----------|---------|
| `build/` | Build artifacts (auto-generated, don't commit) |
| `build/bootstrap/` | Temporal bootstrap binaries |
| `dist/` | Release packages for distribution |
| `tools/` | Dev tools (docker containers, windows build helpers) |
| `scripts/` | Bootstrap bash scripts (3 only) |
| `examples/` | Example programs and tutorials |
| `.claude/` | Agents, skills, templates |

---

## Quick Find Guide

### "I want to..."

**...learn the language**
-> `README.md`, `doc/guide/quick_reference/syntax_quick_reference.md`

**...contribute code**
-> `CLAUDE.md`, `doc/architecture/overview.md`

**...run tests**
-> `bin/simple test`, see `doc/guide/` for test guides

**...build the project**
-> `bin/simple build`, see `CLAUDE.md` for build commands

**...add a standard library feature**
-> `src/lib/`, create tests in `test/unit/std/`

**...fix a compiler bug**
-> `src/compiler/`, tests in `test/unit/compiler/`

**...understand the architecture**
-> `doc/architecture/overview.md`, `doc/architecture/file_class_structure.md`

**...check project status**
-> `doc/EXECUTIVE_SUMMARY.md`, `CHANGELOG.md`

---

## File Naming Conventions

| Pattern | Meaning | Example |
|---------|---------|---------|
| `*_spec.spl` | Test file (SSpec) | `array_spec.spl` |
| `*_utils.spl` | Utility functions | `string_utils.spl` |
| `mod.spl` | Module entry point | `src/lib/mod.spl` |
| `main.spl` | Application entry | `src/app/cli/main.spl` |
| `*.sdn` | Simple Data Notation config | `simple.sdn` |

---

## What NOT to Edit

### Auto-Generated (Don't Commit)

- `build/` - Build artifacts
- `tmp/` - Temporary files
- `.simple-test-checkpoint.sdn` - Test checkpoints
- `target/` - Cargo build output (if exists)

### Auto-Updated (Committed but auto-generated)

- `doc/feature/feature.md` - Generated from tests
- `doc/test/test_result.md` - Generated from test runs
- `doc/bug/bug_report.md` - Generated from bug DB

### Infrastructure (Edit with Caution)

- `.github/workflows/` - CI/CD workflows
- `verification/` - Formal verification code

---

## Related Documentation

- **[Architecture Overview](../../architecture/overview.md)** - High-level architecture
- **[Comprehensive Inventory](../../architecture/file_class_structure.md)** - Detailed file analysis
- **[CLAUDE.md](../../../CLAUDE.md)** - Development guide
- **[README.md](../../../README.md)** - Project introduction
