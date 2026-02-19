# scripts/ Directory - Automation Scripts

**Purpose:** Build, test, and migration automation
**Language:** 100% Pure Simple (.spl) and shell scripts (.ssh)
**Organization:** By function (build, test, migration, audit, setup)

---

## 📋 Directory Structure

```
scripts/
├── build/              # Build automation
├── test/               # Test automation
├── bootstrap/          # Bootstrap scripts
├── migration/          # Code migration tools
├── audit/              # Code auditing
├── setup/              # Environment setup
├── tools/              # Development tools
├── analysis/           # Code analysis
├── debug/              # Debugging tools
├── profiling/          # Performance profiling
├── privilege/          # Privilege management
├── jj-wrappers/        # Jujutsu (jj) helper scripts
├── resource/           # Resource management scripts
└── simple_scripts/     # Simple-specific scripts
```

---

## 🔧 Primary Categories

### build/ (Build Automation)
**Purpose:** Compile and build automation

**Key scripts:**
- `build-bootstrap.sh` - Bootstrap compiler build
- `build-bootstrap-multi-platform.sh` - Multi-platform bootstrap
- `build-bootstrap.spl` - Simple-based bootstrap
- `build-ffi.spl` - FFI compilation
- `build_libstd.spl` - Standard library build
- `build_qemu.spl` - QEMU build
- `compile_with_objects.spl` - Object-based compilation
- `build-minimal-bootstrap.sh` - Minimal bootstrap (moved from bin/)

**When to use:** Building the compiler or libraries

---

### test/ (Test Automation)
**Purpose:** Automated testing scripts

**Key scripts:**
- `test_bootstrap.spl` - Bootstrap testing
- `test_bootstrap_simple.spl` - Simplified bootstrap test
- `test_build_system.spl` - Build system verification
- `test_compile.spl` - Compilation testing
- `test_coverage.spl` - Code coverage testing
- `test_coverage_run.spl` - Coverage execution
- `test_cross_platform_all.spl` - Cross-platform testing
- `test_debug_module.spl` - Debug module testing
- `test_orchestrator.spl` - Test orchestration
- `test_quality.spl` - Code quality checks
- `verify-torch-ffi.sh` - Torch FFI verification (moved from bin/)

**Platform-specific:**
- `test_freebsd_qemu.spl` - FreeBSD QEMU testing
- `test_macos_qemu.spl` - macOS QEMU testing
- `test_windows_mingw.spl` - Windows MinGW testing
- `test_windows_vm.spl` - Windows VM testing

**When to use:** Running automated tests

---

### bootstrap/ (Bootstrap Scripts)
**Purpose:** Multi-stage bootstrap compilation

**Key scripts:**
- `bootstrap-from-scratch.sh` - Complete bootstrap from C++
- `bootstrap-from-scratch.bat` - Windows bootstrap
- `bootstrap-from-scratch-qemu_freebsd.sh` - QEMU FreeBSD environment wrapper

**When to use:** Building from source, self-hosting

---

### migration/ (Code Migration)
**Purpose:** Code transformation and migration tools

**Key scripts:**
- `fix_bare_imports.spl` - Fix bare import statements
- `fix_exports.spl` - Fix export statements
- `fix_new_constructors.spl` - Fix constructor calls
- `bulk_desugar_all.spl` - Bulk desugaring
- `desugar_lazy_seq.spl` - Desugar lazy sequences
- `desugar_lazy_val.spl` - Desugar lazy values
- `find_and_desugar.spl` - Find and desugar patterns
- `migrate_test_db.spl` - Migrate test database
- `migrate_todo.spl` - TODO migration
- `remove_skip_annotations.spl` - Remove test skip annotations
- `reorganize_examples.spl` - Example reorganization (2026-02-16)

**When to use:** Refactoring, upgrading code

---

### audit/ (Code Auditing)
**Purpose:** Code quality and compliance auditing

**Key scripts:**
- `audit_ffi_usage.spl` - Audit FFI usage
- `audit_ffi_wrappers.spl` - Audit FFI wrappers
- `check_imports.spl` - Verify import statements

**When to use:** Code review, quality checks

---

### setup/ (Environment Setup)
**Purpose:** Development environment configuration

**Key scripts:**
- `download_images.spl` - Download test images
- `download_qemu.spl` - Download QEMU images
- `setup_freebsd_vm.spl` - FreeBSD VM setup
- `setup_macos_vm.spl` - macOS VM setup
- `setup_qemu.spl` - QEMU setup
- `setup_windows_vm.spl` - Windows VM setup

**When to use:** Setting up development environment

---

### tools/ (Development Tools)
**Purpose:** Miscellaneous development utilities

**Key scripts:**
- `debug_exports.spl` - Debug export statements
- `demo_phase4_simple.spl` - Phase 4 demo
- `generate_backend_docs.spl` - Generate backend documentation
- `generate_runtime_ffi.spl` - Generate runtime FFI bindings
- `get_coverage.spl` - Get coverage report
- `lib_tool.spl` - Library management tool
- `package-dist.spl` - Package distribution
- `process_instruction_dsl.spl` - Process instruction DSL
- `verify_freebsd_workspace.spl` - Verify FreeBSD workspace

**When to use:** Development utilities

---

### analysis/ (Code Analysis)
**Purpose:** Static code analysis

**Scripts:** Code complexity, dependency analysis, metrics

**When to use:** Understanding codebase structure

---

### debug/ (Debugging Tools)
**Purpose:** Debugging utilities

**Scripts:** Debug helpers, trace tools, inspection utilities

**When to use:** Debugging compiler or runtime

---

### profiling/ (Performance Profiling)
**Purpose:** Performance analysis and profiling

**Scripts:** Profiling tools, performance measurement

**When to use:** Optimizing performance

---

### privilege/ (Privilege Management)
**Purpose:** Permission and access control scripts

**Scripts:** Privilege elevation, access management

**When to use:** Scripts requiring elevated permissions

---

### jj-wrappers/ (Jujutsu Helpers)
**Purpose:** Jujutsu (jj) version control helpers

**Scripts:** Convenient wrappers for common jj operations

**When to use:** Simplifying jj workflows

**Note:** Project uses jj (Jujutsu), NOT git!

---

### resource/ (Resource Management)
**Purpose:** Resource file management and generation

**Scripts:** Resource compilation, embedding, optimization

**When to use:** Managing non-code assets (images, data files, etc.)

---

### simple_scripts/ (Simple-Specific Scripts)
**Purpose:** Scripts specific to Simple language development

**Scripts:** Simple language tooling, utilities, helpers

**When to use:** Simple-specific development tasks

---

## 🎯 Common Use Cases

### Building from Source
```bash
# Complete bootstrap
scripts/bootstrap/bootstrap-from-scratch.sh

# FreeBSD target (native or cross)
scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64

# QEMU FreeBSD wrapper
scripts/bootstrap/bootstrap-from-scratch-qemu_freebsd.sh --step=full2
```

### Running Tests
```bash
# Full test suite
scripts/test/test_bootstrap.spl

# Cross-platform
scripts/test/test_cross_platform_all.spl

# Coverage
scripts/test/test_coverage_run.spl
```

### Code Migration
```bash
# Fix imports
scripts/migration/fix_bare_imports.spl src/

# Desugar code
scripts/migration/bulk_desugar_all.spl src/

# Fix constructors
scripts/migration/fix_new_constructors.spl src/
```

### Environment Setup
```bash
# Setup QEMU
scripts/setup/setup_qemu.spl

# Download images
scripts/setup/download_images.spl
```

---

## 📝 Script Conventions

### File Extensions
- **`.spl`** - Simple scripts (Pure Simple)
- **`.ssh`** - Simple shell scripts (Unix-compatible)
- **`.sh`** - Bash scripts (3 bootstrap scripts only)
- **`.bat`** - Windows batch scripts

### Naming Conventions
- Lowercase with underscores: `build_libstd.spl`
- Verb-noun format: `generate_backend_docs.spl`
- Category prefix: `test_bootstrap.spl`, `audit_ffi_usage.spl`

### Shebang Lines
```bash
#!/usr/bin/env simple       # For .spl scripts
#!/bin/bash                 # For .sh scripts (3 only)
```

---

## 🔍 Finding Scripts

### By Function
```bash
# Build scripts
ls scripts/build/

# Test scripts
ls scripts/test/

# Migration scripts
ls scripts/migration/
```

### By Name
```bash
# Find script by keyword
find scripts/ -name "*bootstrap*"
find scripts/ -name "*test*"
```

### By Content
```bash
# Search for functionality
grep -r "function_name" scripts/ --include="*.spl"
```

---

## ✍️ Writing Scripts

### Script Template
```simple
#!/usr/bin/env simple
# Script Name - Brief Description
#
# Usage:
#   scripts/category/script_name.spl [arguments]
#
# Examples:
#   scripts/category/script_name.spl input.spl

use app.io.mod.{shell, file_exists, file_read}

fn main():
    # Implementation
    pass

main()
```

### Best Practices
- ✅ Add usage instructions in header comment
- ✅ Handle errors gracefully
- ✅ Use meaningful variable names
- ✅ Add examples in comments
- ✅ Make scripts idempotent (safe to run multiple times)
- ✅ Test on all platforms (if applicable)

### Guidelines
- **DO use Simple** (.spl) for new scripts
- **DON'T use Bash** unless absolutely necessary
- **DO organize** by function (build, test, etc.)
- **DON'T commit** generated files
- **DO document** usage and examples

---

## 📊 Statistics

**Total Scripts:** 100+
**Categories:** 15 subdirectories
**Language Breakdown:**
- Pure Simple (.spl): ~90%
- Shell scripts (.ssh/.sh): ~10%
- Batch scripts (.bat): 1 file

**By Category:**
- build/: 9 scripts (includes build-minimal-bootstrap.sh from bin/)
- test/: 30+ scripts (includes verify-torch-ffi.sh from bin/)
- bootstrap/: 3 scripts
- migration/: 11 scripts
- audit/: 3 scripts
- setup/: 6 scripts
- tools/: 10 scripts
- resource/: New category
- simple_scripts/: New category
- Other: 30+ scripts

---

## 🔄 Recent Changes

### 2026-02-16: Major Reorganization
**Scripts moved from bin/ to proper categories:**
- ✅ `build-minimal-bootstrap.sh` → `scripts/build/`
- ✅ `verify-torch-ffi.sh` → `scripts/test/`

**Scripts organized into subdirectories:**
- ✅ All scripts moved from `scripts/` root to category subdirectories
- ✅ Created 15 category directories (was 12, added 3 new)
- ✅ New categories: `resource/`, `simple_scripts/`

**Reason:** Better organization, clearer purpose, easier to find scripts

---

## 🔗 Related Directories

- **bin/** - Executable wrappers (not scripts)
- **build/** - Build artifacts (script outputs)
- **tools/** - Development tools (seed compiler, Docker)

---

## 🚀 Running Scripts

### Direct Execution
```bash
# Simple scripts
bin/simple scripts/build/build_libstd.spl

# Shell scripts
scripts/bootstrap/bootstrap-from-scratch.sh
```

### With Arguments
```bash
# Pass arguments
bin/simple scripts/migration/fix_bare_imports.spl src/app/

# Multiple files
bin/simple scripts/audit/check_imports.spl src/ test/
```

### In CI/CD
Scripts are designed to be CI/CD friendly:
- Exit codes indicate success/failure
- Stdout for output, stderr for errors
- No interactive prompts

---

## 📚 Documentation

Each major script category should have:
- Header comments explaining purpose
- Usage instructions
- Example invocations
- Error handling documentation

**For complex scripts:** Consider adding docs in `doc/workflow/`

---

## 🛠️ Maintenance

### Monthly Tasks
- Review script usage (identify unused scripts)
- Update documentation
- Test cross-platform compatibility
- Archive obsolete scripts

### Per Release
- Update version references
- Test all bootstrap scripts
- Verify migration scripts work
- Update README references

---

## 🆘 Troubleshooting

### Script Not Found
**Check:**
1. Is it in the right category? (`find scripts/ -name "*script*"`)
2. Is it executable? (`chmod +x scripts/category/script.spl`)
3. Was it moved? (check git/jj log)

### Permission Denied
```bash
# Make executable
chmod +x scripts/category/script.spl

# Or run through runtime
bin/simple scripts/category/script.spl
```

### Script Fails
1. **Read error message** - Usually explains the issue
2. **Check dependencies** - May require setup
3. **Run with debug** - Add `set -x` for shell scripts
4. **Check platform** - May be platform-specific

---

**Last Updated:** 2026-02-16
**Maintainer:** Build & Infrastructure Team
**Language:** 100% Pure Simple (goal: eliminate all shell scripts)
**Quality:** All build/test scripts tested and working ✅
