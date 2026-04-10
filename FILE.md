# Simple Language Compiler - Root Directory

**Version:** 0.6.1
**Purpose:** Top-level project organization and entry points
**Quick Start:** See [CLAUDE.md](CLAUDE.md) for development guide

---

## 📋 Quick Reference

| File/Directory | Purpose | When to Use |
|----------------|---------|-------------|
| **CLAUDE.md** | Development guide | Start here for development |
| **README.md** | Project overview | Learn what Simple is |
| **AGENTS.md** | Agent definitions | Using Task tool subagents |
| **.sstack/** | Session state tracking | Local workflow state and phase handoff notes |
| **bin/** | Executables & CLI | Running Simple commands |
| **src/** | Source code | Core implementation |
| **test/** | Test suites | Testing & verification |
| **examples/** | Example programs | Learning Simple |
| **doc/** | Documentation | Guides, specs, reports |
| **scripts/** | Automation scripts | Build, test, migration |
| **tools/** | Development tools | Seed compiler, Docker |

---

## 📚 Essential Files

### CLAUDE.md (Primary Development Guide)
**Size:** ~15KB | **Audience:** Developers

**Complete development reference:**
- ✅ Agent definitions for Task tool
- ✅ Skills reference (/versioning, /test, /coding, etc.)
- ✅ Critical rules (jj not git, no git branches, etc.)
- ✅ Quick commands (build, test, run)
- ✅ Syntax essentials
- ✅ Project structure overview
- ✅ SFFI (Simple FFI) patterns
- ✅ Runtime limitations
- ✅ Container testing guide

**Use CLAUDE.md as your primary reference!**

---

### AGENTS.md (Symbolic Link)
Points to: `CLAUDE.md`

Convenience link for agent-based workflows. Same content as CLAUDE.md.

---

### .sstack/ (Session State Tracking)
**Audience:** Local development workflows

Stores per-task state handoff files used by the repo's stacked workflow.

- Contains `TASKS.md` plus per-feature `state.md` files
- Intended to stay in the project root as workflow metadata
- Not user-facing documentation or source code

---

### README.md (Project Overview)
**Size:** ~8KB | **Audience:** General public

**Project introduction:**
- What is Simple Language
- Key features (100% self-hosted, pure Simple implementation)
- Installation instructions
- Quick examples
- Build status
- License information

**External-facing documentation** for GitHub visitors.

---

### VERSION
**Format:** Semantic versioning (0.5.1)

Current version string used by:
- CLI (`bin/simple --version`)
- Build system
- Release packaging
- MCP server identification

---

### CHANGELOG.md
**Format:** Keep a Changelog standard

**Version history:**
- 0.6.1 - Current release
- 0.6.0 - Previous release
- 0.5.x - Earlier releases
- Format: Added/Changed/Deprecated/Removed/Fixed/Security

**Update on every release.**

---

### install.shs
**Automated installation script**

**Purpose:** Install Simple system-wide

**Usage:**
```bash
# Default installation
./install.shs

# Custom prefix
PREFIX=/usr/local ./install.shs

# See installation options
./install.shs --help
```

**Features:**
- Platform detection (Linux, macOS, FreeBSD, Windows)
- Multi-architecture support
- Creates symlinks in /usr/local/bin
- Installs man pages
- Sets up shell completions

**Note:** Can also install manually by copying `bin/simple` to PATH.

---

## 📁 Core Directories

### bin/ (Executables & CLI)
**Purpose:** Compiled binaries, CLI wrappers, MCP servers

**Key files:**
- `simple` - Main CLI (auto-detects platform)
- `simple_mcp_server` - MCP server for Claude Code
- `release/` - Multi-platform binaries (335MB)
- `FILE.md` - Complete bin/ documentation

**See:** [bin/FILE.md](bin/FILE.md)

---

### src/ (Source Code)
**Purpose:** Simple language implementation (100% self-hosted)

**Structure:**
```
src/
├── app/        # Applications (cli, build, mcp, test_runner, desugar)
├── lib/        # Standard library (common, nogc_sync_mut, nogc_async_mut, gc_async_mut)
├── compiler/   # Unified compiler (00.common → 99.loader, numbered layers)
├── runtime/    # Native runtime and support libraries
└── i18n/       # Internationalization
```

**All code in `.spl` (Simple) files!**

---

### test/ (Test Suites)
**Purpose:** 4,067 passing tests (100% success rate)

**Structure:**
```
test/
├── unit/           # Unit tests (3,500+ tests)
├── integration/    # Integration tests
├── system/         # System tests (LLM, end-to-end)
└── benchmarks/     # Performance benchmarks
```

**Run tests:** `bin/simple test test/unit/spec.spl`

---

### examples/ (Example Programs)
**Purpose:** 215 examples organized by topic (01-11 categories)

**Structure:** Numbered learning path
- 01_getting_started - Hello world
- 02_language_features - Syntax demos
- 03_concurrency - Async, actors
- 04-11 - Data formats, stdlib, I/O, ML, GPU, embedded, tooling, advanced
- experiments/ - WIP research
- projects/ - Full applications (medgemma_korean)

**See:** [examples/FILE.md](examples/FILE.md)

---

### doc/ (Documentation)
**Purpose:** Comprehensive project documentation (2,000+ files)

**Categories (numbered):**
- 01_research/ - Research (local impl, domain/external)
- 02_requirements/ - Requirements (feature, nfr, ui)
- 03_plan/ - Plans (arch, design, sys_test, agent_tasks)
- 04_architecture/ - Architecture (ADRs, rules, formats)
- 05_design/ - Design documents
- 06_spec/ - SSpec-generated specs
- 07_guide/ - User guides, tutorials
- 08_tracking/ - Bug, test, todo, task tracking
- 09_report/ - Implementation reports
- 10_metrics/ - Dashboards, coverage

**See:** [doc/FILE.md](doc/FILE.md)

---

### scripts/ (Automation Scripts)
**Purpose:** Build, test, and migration automation

**Structure:**
- build/ - Build scripts
- test/ - Test scripts
- migration/ - Migration tools
- bootstrap/ - Bootstrap scripts
- audit/ - Code auditing
- setup/ - Environment setup

**All scripts in `.spl` or `.shs` format (Pure Simple!)**

**See:** [scripts/FILE.md](scripts/FILE.md)

---

### tools/ (Development Tools)
**Purpose:** Build tools and containers

**Contents:**
- `seed/` - Seed compiler (C++ bootstrap)
- `docker/` - Docker containers for testing
- `qemu/` - QEMU images for cross-platform testing
- `mold/` - Mold linker for fast linking

---

### build/ (Build Artifacts)
**Purpose:** Compiled outputs and build cache

**Contents:**
- `artifacts/` - Compiled binaries
- `bootstrap/` - Bootstrap stages
- `coverage/` - Coverage reports
- `dist/` - Distribution packages

**Note:** Generated during build, not committed to version control.

**See:** [build/FILE.md](build/FILE.md)

---

## 🏗️ Build & Development

### Quick Build
```bash
# Debug build (fast compilation)
bin/simple build

# Release build (optimized)
bin/simple build --release

# Test
bin/simple test

# Run example
bin/simple run examples/01_getting_started/hello_native.spl
```

### Bootstrap Build
```bash
# Multi-stage bootstrap from source
scripts/bootstrap/bootstrap-from-scratch.sh

# Quick bootstrap (existing binary)
bin/simple build bootstrap-check
```

### Container Testing
```bash
# Isolated testing environment
docker-compose -f config/docker-compose.yml up unit-tests

# See doc/guide/container_testing.md for details
```

---

## 📦 Installation

### From Release Binary
```bash
# Download and extract
curl -L https://github.com/simple-lang/simple/releases/latest/download/simple-linux-x86_64.tar.gz | tar xz

# Run
./bin/simple --version
```

### From Source
```bash
# Clone repository (use jj, not git!)
jj git clone https://github.com/simple-lang/simple.git
cd simple

# Build (uses pre-built runtime)
bin/simple build --release

# Install system-wide
./install.shs
```

### Using install.shs (Recommended)
```bash
# Automated installation with platform detection
./install.shs

# Custom installation prefix
PREFIX=/usr/local ./install.shs

# See available options
./install.shs --help
```

**Note:** Use `bin/simple build` commands directly (no Makefile).

---

## 🧪 Testing

### Run All Tests (4,067 tests)
```bash
bin/simple test                    # All tests (~17 seconds)
bin/simple test test/unit/         # Unit tests only
bin/simple test path/to/spec.spl   # Single file
```

### Test Categories
```bash
bin/simple test test/unit/              # Unit tests (3,500+)
bin/simple test test/integration/       # Integration tests
bin/simple test test/system/            # System tests
bin/simple test test/benchmarks/        # Performance benchmarks
```

### Container Testing
```bash
# Reproducible isolated environment
docker-compose -f config/docker-compose.yml up all-tests
```

---

## 📖 Documentation

### For Developers
- **Start:** [CLAUDE.md](CLAUDE.md) - Complete development guide
- **Skills:** `.claude/skills/` - Skill documentation (/test, /coding, etc.)
- **Agents:** `.claude/agents/` - Agent definitions

### For Users
- **README:** [README.md](README.md) - Project overview
- **Guides:** [doc/guide/](doc/guide/) - User guides
- **Examples:** [examples/](examples/) - Code examples
- **Specs:** [doc/spec/](doc/spec/) - Language specifications

### For Contributors
- **Contributing:** [doc/contributing/](doc/contributing/) - Contribution guidelines
- **Architecture:** [doc/architecture/](doc/architecture/) - System design
- **API Docs:** [doc/api/](doc/api/) - API documentation

---

## 🔧 Configuration Files

### .claude/ (Claude Code Integration)
**Purpose:** Agent definitions, skills, templates

**Structure:**
```
.claude/
├── agents/         # Task tool agent definitions
├── skills/         # Skill documentation
├── templates/      # Code templates
└── keybindings.json # Keyboard shortcuts
```

**Used by Claude Code for AI-assisted development.**

---

### config/ (Project Configuration)
**Purpose:** Build and deployment configurations

**Contents:**
- `docker-compose.yml` - Container orchestration
- `packaging/` - Package specs (Debian, Homebrew, RPM, Windows)
- `simple.sdn` - Project settings (SDN format)

---

### .github/ (GitHub Configuration)
**Purpose:** CI/CD workflows, issue templates

**Contents:**
- `workflows/` - GitHub Actions
- `ISSUE_TEMPLATE/` - Issue templates
- `PULL_REQUEST_TEMPLATE.md` - PR template

---

## 🎯 Common Workflows

### Development Workflow
```bash
# 1. Make changes to src/
vim src/app/cli/main.spl

# 2. Test changes
bin/simple test test/unit/app/cli/

# 3. Build
bin/simple build

# 4. Commit (use jj, not git!)
jj describe -m "fix: update CLI help text"
jj bookmark set main -r @
jj git push --bookmark main
```

### Adding Examples
```bash
# 1. Create example in appropriate category
vim examples/03_concurrency/my_example.spl

# 2. Test it runs
bin/simple run examples/03_concurrency/my_example.spl

# 3. Update examples/README.md if needed
# 4. Commit
```

### Adding Tests
```bash
# 1. Create spec file
vim test/unit/my_feature_spec.spl

# 2. Run test
bin/simple test test/unit/my_feature_spec.spl

# 3. Verify all tests still pass
bin/simple test

# 4. Commit
```

---

## 🚧 Version Control

**CRITICAL:** Use `jj` (Jujutsu), **NOT git!**

```bash
# See current changes
jj status

# Describe changes
jj describe -m "commit message"

# Push to remote
jj bookmark set main -r @
jj git push --bookmark main

# Never use: git add, git commit, git push
```

**See:** `.claude/skills/versioning.md` for complete jj workflow

---

## 📊 Project Statistics

**Version:** 0.6.1
**Language:** 100% Simple (self-hosted)
**Source Files:** 623,000+ lines
**Tests:** 4,067 tests (100% passing)
**Examples:** 215 examples
**Documentation:** 2,000+ files
**Platforms:** Linux, macOS, FreeBSD, Windows (x86_64, ARM64, RISC-V)

---

## 🔗 Important Links

**Repository:** https://github.com/simple-lang/simple
**Documentation:** https://simple-lang.org/docs
**Releases:** https://github.com/simple-lang/simple/releases
**Issues:** https://github.com/simple-lang/simple/issues
**Discussions:** https://github.com/simple-lang/simple/discussions

---

## 📄 License

**License:** MIT License (see LICENSE file)
**Third-party notices:** See THIRD_PARTY_NOTICES.md for vendored runtime components
**Copyright:** 2024-2026 Simple Language Contributors

---

## 🆘 Getting Help

### Quick Help
```bash
bin/simple --help              # CLI help
bin/simple test --help         # Test help
bin/simple build --help        # Build help
```

### Documentation
- CLAUDE.md - Development guide
- doc/guide/ - User guides
- examples/ - Code examples

### Community
- GitHub Issues - Bug reports
- GitHub Discussions - Questions & ideas
- Discord - Real-time chat (link in README)

---

## 📝 File Naming Conventions

**Simple source:** `.spl`
**Shell scripts:** `.shs` (Simple shell script)
**Module format:** `.smf` (Simple module format - compiled)
**Configuration:** `.sdn` (Simple Data Notation)
**Documentation:** `.md` (Markdown)

---

**Last Updated:** 2026-02-16
**Maintained By:** Simple Language Team
**Contributors:** 50+ contributors (see CONTRIBUTORS.md)
