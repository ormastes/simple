# Simple Language - Project Structure Guide

**Quick Navigation:** Where to find what you're looking for

**Last Updated:** 2026-02-16
**For detailed analysis:** See [doc/architecture/file_class_structure.md](../architecture/file_class_structure.md)

---

## 📂 Root Directory Overview

```
simple/
├── 📄 Essential Files (5 files)
├── 📁 Source Code (src/)
├── 📁 Tests (test/)
├── 📁 Documentation (doc/)
├── 📁 Configuration (config/)
├── 📁 Scripts & Tools (scripts/, tools/)
├── 📁 Build & Distribution (bin/, build/, dist/)
└── 📁 Supporting Files (tools/, examples/, config/, etc.)
```

---

## 📄 Root Files (Essential Only)

### **Project Documentation**

| File | Purpose | Read When |
|------|---------|-----------|
| `README.md` | Main project introduction, quick start | First time visiting |
| `CLAUDE.md` | Development guide, coding standards | Contributing code |
| `AGENTS.md` | Agent definitions → redirects to CLAUDE.md | Looking for agents |
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

## 📁 Main Directories

### **Source Code: `src/`** (111,044 lines, production code)

```
src/
├── core/           # Core Simple library (17,871 lines)
│   ├── lexer.spl, parser.spl           # Language parsing
│   ├── ast.spl, mir.spl                # Intermediate representations
│   ├── interpreter/                     # Tree-walk interpreter
│   └── compiler/                        # C code generation (for seed bootstrap)
│
├── std/            # Standard library (192,427 lines)
│   ├── spec.spl                         # Testing framework (SSpec)
│   ├── string.spl, array.spl            # Core data types
│   ├── math.spl, path.spl               # Utilities
│   ├── platform/                        # Cross-platform abstraction
│   ├── json/, cbor/, yaml/              # Serialization
│   ├── http/, tcp/, udp/                # Networking
│   └── crypto/, gpu/, ml/               # Advanced features
│
├── app/            # Applications & tools (129,154 lines)
│   ├── cli/                             # Command-line interface
│   ├── build/                           # Build system
│   ├── test_runner_new/                 # Test runner
│   ├── mcp/                             # MCP servers (file I/O, debug)
│   ├── mcp_jj/                          # Jujutsu VCS MCP
│   ├── lsp/                             # Language Server Protocol
│   ├── dap/                             # Debug Adapter Protocol
│   └── desugar/                         # Code transformations
│
├── compiler/       # Full compiler (140,341 lines)
│   ├── parser.spl, lexer.spl            # Full-featured parser
│   ├── backend/                         # 8 backends (LLVM, Cranelift, etc.)
│   ├── mir_opt/                         # MIR optimizations
│   └── type_system/                     # Type checking & inference
│
├── compiler/         # Unified compiler — numbered layers (see below)
│   └── 10.frontend/core/  # Core frontend (lexer, parser, AST, interpreter)
│
├── lib/            # Core libraries (30,993 lines)
│   ├── database/                        # BugDB, TestDB, FeatureDB
│   ├── pure/                            # Pure functional ML library
│   ├── parser/                          # Parser library
│   └── qemu/                            # QEMU integration
│
├── baremetal/      # Bare-metal runtime (4,829 lines)
├── remote/         # Remote execution (3,964 lines)
└── ffi/            # FFI bridge utilities (1,808 lines)
```

**Go here when:**
- Writing new features → `src/lib/` or `src/app/`
- Fixing compiler bugs → `src/compiler/`
- Adding ML features → `src/lib/ml/` or `src/lib/pure/`
- Building tools → `src/app/`

---

### **Tests: `test/`** (512,000+ lines, 4,067 tests)

```
test/
├── unit/           # Unit tests (most tests here)
│   ├── std/                            # Standard library tests
│   ├── app/                            # Application tests
│   ├── core/                           # Core language tests
│   └── compiler/                       # Compiler tests
│
├── integration/    # Integration tests
├── system/         # System/end-to-end tests
├── benchmarks/     # Performance benchmarks (executable, not test specs)
│   ├── compiler_runtime.spl            # Core benchmark framework
│   ├── pure_dl_perf.spl                # DL performance benchmarks
│   └── run_duplicate_check.spl         # Duplicate detection benchmarks
│
└── lib/            # Test utilities & symlinks
```

**Go here when:**
- Writing tests for new features → `test/unit/`
- Testing integration → `test/integration/`
- End-to-end testing → `test/system/`
- Measuring performance → `test/benchmarks/`

---

### **Documentation: `doc/`** (40MB, 2,567 directories)

```
doc/
├── 📋 Status Reports
│   ├── EXECUTIVE_SUMMARY.md            # High-level project status
│   ├── PRODUCTION_READINESS.md         # Deployment assessment
│   └── FEATURES_THAT_WORK.md          # Working features catalog
│
├── 📖 User Guides (guide/)
│   ├── quick_reference/                # Quick reference guides
│   │   ├── syntax_quick_reference.md   # Language syntax
│   │   └── ...                         # Other quick references
│   ├── async_guide.md                  # Async programming
│   ├── lsp_integration.md              # Editor setup
│   ├── backend/                        # Compiler backends
│   │   ├── capabilities.md            # Backend selection & capabilities
│   │   ├── shared_components.md       # Shared type mapping utilities
│   │   ├── phase2_native_linker.md    # Native linker implementation
│   │   ├── phase3_llvm.md             # LLVM backend implementation
│   │   ├── vhdl.md                    # VHDL/FPGA backend
│   │   └── vulkan.md                  # Vulkan GPU backend
│   └── folder_file.md                  # This file!
│
├── 🏗️ Architecture (architecture/)
│   ├── overview.md                     # High-level architecture
│   ├── file_class_structure.md         # Comprehensive inventory
│   ├── architecture.md                 # Module dependencies
│   └── architecture_modules.md         # Module details
│
├── 🔬 Technical (design/, research/, plan/)
│   ├── design/                         # Design documents
│   ├── research/                       # Research notes
│   └── plan/                           # Implementation plans
│
└── 📊 Generated (feature/, test/, bug/)
    ├── feature/                        # Feature tracking
    ├── test/                           # Test results
    └── bug/                            # Bug reports
```

**Go here when:**
- Learning the language → `doc/guide/`
- Understanding architecture → `doc/architecture/`
- Checking status → Root `doc/*.md` files
- Planning features → `doc/design/`, `doc/plan/`

---

### **Configuration: `config/`** (9 files)

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
| `README_DOCKER.md` | Docker usage guide | Docker users |

**Go here when:**
- Changing GPU device → Edit `dl.config.sdn`
- Adjusting test config → Edit `simple.test.sdn`
- Docker setup → Read `README_DOCKER.md`

**Important:** Use `-f config/` flag for Docker Compose:
```bash
docker-compose -f config/docker-compose.yml up
```

---

### **Scripts: `scripts/`** (51MB)

```
scripts/
├── analysis/       # Code analysis tools
├── debug/          # Debug utilities
├── build/          # Build scripts
└── [various .spl and .sh files]
```

**Common scripts:**
- Bootstrap scripts: `bootstrap-*.sh`
- Build automation: `build-*.sh`, `build-*.spl`
- Testing: `test-*.spl`

**Go here when:**
- Running bootstraps → `scripts/bootstrap-*.sh`
- Build automation → `scripts/build/`
- Analysis tools → `scripts/analysis/`

---

### **Binaries: `bin/`** (779MB)

```
bin/
├── simple              # Current build (debug)
└── release/
    └── simple          # Pre-built runtime (33MB)
```

**Usage:**
- `bin/simple` - Run Simple commands
- `bin/release/simple` - Stable pre-built version

---

### **Build Artifacts: `build/`** (3.6GB)

Build directory for compilation outputs. **Auto-generated, don't commit.**

---

### **Distribution: `dist/`** (859MB)

```
dist/
├── simple-0.5.0-linux-x86_64/
├── simple-0.5.0-darwin-arm64/
├── simple-0.5.0-windows-x86_64/
└── [other platform packages]
```

Release packages for distribution. **Generated by build system.**

---

### **Development Tools: `tools/`** (111MB)

```
tools/
├── seed/           # Bootstrap compiler (C/C++)
│   ├── seed.c          # C seed compiler
│   ├── runtime.c/h     # Runtime implementation
│   ├── ARCHITECTURE.md # Bootstrap architecture
│   └── README.md       # Bootstrap guide
│
└── docker/         # Container infrastructure
    ├── Dockerfile.test-isolation   # Minimal test container
    ├── Dockerfile.test-full        # Full dev container
    ├── README_TEST_CONTAINERS.md   # Container docs
    └── [platform Dockerfiles]
```

**Purpose:** Development and build tools.
- **seed/** - C/C++ bootstrap compiler for building Simple from scratch
- **docker/** - Containerized testing and development environments

**Go here when:**
- Understanding bootstrap process
- Porting to new platforms
- Debugging low-level issues
- Setting up container-based testing

---

### **Examples: `examples/`** (1.3MB)

Example programs and tutorials.

**Categories:**
- Basic language features
- ML/Deep learning examples
- Game development
- Physics simulations

---

### **Other Directories**

| Directory | Size | Purpose |
|-----------|------|---------|
| `tools/` | 111MB | Dev tools (seed compiler, docker) |
| `verification/` | 4.8GB | Formal verification (Lean 4) |
| `release/` | 160MB | Release artifacts |
| `archive/` | 292KB | Archived/obsolete code |
| `src/i18n/` | 244KB | Internationalization |
| `src/app/` | 88KB | Editor integrations (nvim_plugin, vscode_extension) |
| `boards/` | - | Hardware board configs |
| `config/packaging/` | - | Package metadata (Debian, RPM, Homebrew, Windows) |
| `resources/` | - | Resource files |
| `tmp/` | - | Temporary files (gitignored) |

---

## 🔍 Quick Find Guide

### "I want to..."

**...learn the language**
→ `README.md`, `doc/guide/quick_reference/syntax_quick_reference.md`

**...contribute code**
→ `CLAUDE.md`, `doc/architecture/overview.md`

**...run tests**
→ `bin/simple test`, see `doc/guide/` for test guides

**...run benchmarks**
→ `test/benchmarks/`, see `test/benchmarks/README.md`

**...build the project**
→ `bin/simple build`, see `CLAUDE.md` for build commands

**...use Docker**
→ `config/README_DOCKER.md`, `config/docker-compose.yml`

**...write documentation**
→ `doc/guide/` for user guides, `doc/design/` for technical docs

**...add a standard library feature**
→ `src/lib/`, create tests in `test/unit/std/`

**...fix a compiler bug**
→ `src/compiler/`, tests in `test/unit/compiler/`

**...understand the architecture**
→ `doc/architecture/overview.md`, `doc/architecture/file_class_structure.md`

**...check project status**
→ `doc/EXECUTIVE_SUMMARY.md`, `CHANGELOG.md`

**...configure tools**
→ `config/` directory, edit relevant `.sdn` files

**...find a specific file**
→ Use: `find . -name "filename.spl"`

**...search for code**
→ Use: `grep -r "search_term" src/`

---

## 📊 Project Statistics

| Metric | Value |
|--------|-------|
| **Total .spl files** | 2,649 |
| **Total lines of code** | 623,207 |
| **Source code (src/)** | 111,044 lines |
| **Test code (test/)** | ~512,000 lines |
| **Tests passing** | 4,067/4,067 (100%) ✅ |
| **Documentation files** | 2,567 directories |

---

## 🎯 Common Tasks

### Adding a New Feature

1. **Write the code** → `src/lib/` or `src/app/`
2. **Write tests** → `test/unit/`
3. **Update docs** → `doc/guide/` or docstrings
4. **Test it** → `bin/simple test`
5. **Commit** → Use `jj` (not git!)

### Running Tests

```bash
# All tests
bin/simple test

# Specific file
bin/simple test test/unit/std/array_spec.spl

# In Docker (isolated)
docker-compose -f config/docker-compose.test.yml run test-isolation
```

### Building

```bash
# Debug build
bin/simple build

# Release build
bin/simple build --release

# Bootstrap rebuild
bin/simple build bootstrap-rebuild
```

### Documentation

```bash
# Check doc coverage
bin/simple doc-coverage

# Build with doc warnings
bin/simple build --warn-docs

# Run doc tests
bin/simple test --sdoctest
```

---

## 📝 File Naming Conventions

### Simple Source Files

| Pattern | Meaning | Example |
|---------|---------|---------|
| `*_spec.spl` | Test file (SSpec) | `array_spec.spl` |
| `*_utils.spl` | Utility functions | `string_utils.spl` |
| `mod.spl` | Module entry point | `src/lib/mod.spl` |
| `main.spl` | Application entry | `src/app/cli/main.spl` |

### Configuration Files

| Pattern | Meaning | Example |
|---------|---------|---------|
| `*.sdn` | Simple Data Notation config | `simple.sdn` |
| `*.yml` | YAML config (Docker) | `docker-compose.yml` |

### Documentation Files

| Pattern | Meaning | Example |
|---------|---------|---------|
| `README.md` | Directory overview | `doc/README.md` |
| `*_guide.md` | User guide | `async_guide.md` |
| `*_spec.md` | Specification | `language_spec.md` |

---

## 🚨 What NOT to Edit

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
- `seed/` - Bootstrap compiler (C/C++)
- `verification/` - Formal verification code

---

## 💡 Tips

### Quick Navigation

```bash
# Use aliases
alias s='bin/simple'
alias st='bin/simple test'
alias sb='bin/simple build'

# Then:
s test test/unit/std/
sb --release
```

### Finding Files

```bash
# Find by name
find . -name "*array*"

# Find by type
find . -name "*.spl" -type f

# Exclude build dirs
find . -name "*.spl" -not -path "./build/*" -not -path "./tmp/*"
```

### Searching Code

```bash
# Search in source
grep -r "function_name" src/

# Search in tests
grep -r "describe" test/

# Case-insensitive
grep -ri "TODO" src/
```

---

## 📚 Related Documentation

- **[Architecture Overview](../architecture/overview.md)** - High-level architecture
- **[Comprehensive Inventory](../architecture/file_class_structure.md)** - Detailed file analysis
- **[CLAUDE.md](../../CLAUDE.md)** - Development guide
- **[README.md](../../README.md)** - Project introduction

---

**Last Updated:** 2026-02-16
**Maintained by:** Claude Sonnet 4.5
**Status:** Production Ready ✅
