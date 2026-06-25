# Release Notes: v0.4.0-beta.5

**Release Date:** 2026-02-04
**Release URL:** https://github.com/ormastes/simple/releases/tag/v0.4.0-beta.5

## 🎯 Highlights

**Simple Module Unfold Refactoring** - Major module structure improvement applying the "unfold package pattern" to 22 Simple module subdirectories.

**Two Optimized Builds:**
- ✅ **Bootstrap: 13 MB** (50% smaller - recommended)
- ✅ **Release: 26 MB** (standard optimizations)

## 📦 Downloads

### Recommended: Bootstrap Build (13 MB)

```bash
# Download
wget https://github.com/ormastes/simple/releases/download/v0.4.0-beta.5/simple_runtime-bootstrap

# Install
chmod +x simple_runtime-bootstrap
sudo mv simple_runtime-bootstrap /usr/local/bin/simple

# Verify
simple --version
```

### Alternative: Full Release Build (26 MB)

```bash
# Download
wget https://github.com/ormastes/simple/releases/download/v0.4.0-beta.5/simple_runtime-release

# Install
chmod +x simple_runtime-release
sudo mv simple_runtime-release /usr/local/bin/simple
```

## 🔄 What Changed

### Module Structure Refactoring

Transformed **22 module subdirectories** using unfold pattern: `a/b/` → `a.b/`

**Before:**
```
src/app/interpreter/
  ├── async_runtime/
  ├── control/
  ├── core/
  └── ... (14 subdirectories)
```

**After:**
```
src/app/
  ├── interpreter/              # Main module (files only)
  ├── interpreter.async_runtime/ # Unfolded submodule
  ├── interpreter.control/       # Unfolded submodule
  ├── interpreter.core/          # Unfolded submodule
  └── ... (14 unfolded modules visible at top level)
```

### Modules Unfolded

**Interpreter (14 modules):**
- `interpreter.async_runtime/` - Async runtime (actors, futures, generators)
- `interpreter.call/` - Function calls and dispatch
- `interpreter.collections/` - Persistent data structures
- `interpreter.control/` - Control flow (if, loops, match)
- `interpreter.core/` - Core interpreter engine
- `interpreter.expr/` - Expression evaluation
- `interpreter.extern/` - External FFI functions
- `interpreter.ffi/` - FFI bridge
- `interpreter.helpers/` - Helper utilities
- `interpreter.lazy/` - Lazy evaluation
- `interpreter.memory/` - Memory management
- `interpreter.module/` - Module system
- `interpreter.perf/` - Performance tracking
- `interpreter.utils/` - Common utilities

**Other Modules (8 modules):**
- `lsp.handlers/` - LSP protocol handlers
- `dashboard.views/` - Dashboard UI views
- `dashboard.render/` - Rendering utilities
- `web_dashboard.api/` - Web API endpoints
- `web_dashboard.static/` - Static assets
- `package.registry/` - Package registry client
- `ffi_gen.specs/` - FFI generation specs (43 files)
- `ffi_gen.templates/` - FFI templates (12 files)

## ✨ Benefits

1. **Visible Hierarchy**
   - Module relationships clear at directory level
   - `ls src/app/` shows all interpreter.* modules grouped together

2. **Easier Navigation**
   - No need to `cd` into parent directories
   - Related modules alphabetically grouped by prefix

3. **Zero Code Changes**
   - Import paths unchanged (already use dot notation)
   - 152 files moved, 0 lines of code changed
   - Backward compatible

4. **Clearer Organization**
   - Related modules visibly clustered
   - Hierarchy explicit in directory names

## 📊 Binary Comparison

| Build | Size | Optimization | Strip | LTO | Use Case |
|-------|------|--------------|-------|-----|----------|
| **Bootstrap** | **13 MB** | `opt-level = "z"` | ✅ Yes | ✅ Yes | **Distribution** ✅ |
| **Release** | **26 MB** | `opt-level = 3` | ❌ No | ✅ Yes | Development |

**Size Reduction:** 50% smaller with bootstrap build (13 MB vs 26 MB)

## 🛠️ Technical Details

### Build Commands Used

```bash
# Bootstrap build (13 MB)
cargo build --profile bootstrap

# Release build (26 MB)
cargo build --release
```

### Bootstrap Profile Configuration

```toml
[profile.bootstrap]
inherits = "release"
opt-level = "z"        # Optimize for size
lto = true             # Link-time optimization
codegen-units = 1      # Single codegen unit for better optimization
panic = "abort"        # No unwinding (smaller binary)
strip = true           # Strip symbols (smaller binary)
```

### Statistics

- **Modules refactored:** 22
- **Files moved:** 152
- **Code changes:** 0
- **Import changes:** 0
- **Tests passing:** 631+
- **Build time (bootstrap):** ~2m 42s
- **Build time (release):** ~2m 39s

## 🔍 Verification

Both builds are functionally equivalent:

```bash
# Check version
./simple_runtime-bootstrap --version
./simple_runtime-release --version

# Run same program with both
echo 'print "Hello!"' > test.spl
./simple_runtime-bootstrap test.spl  # Output: Hello!
./simple_runtime-release test.spl    # Output: Hello!

# Compare functionality
diff <(./simple_runtime-bootstrap --help) <(./simple_runtime-release --help)
# No differences - same features
```

## 📝 Migration Notes

**No migration needed!** This is a structure-only change.

- ✅ All existing imports work unchanged
- ✅ All existing scripts work unchanged
- ✅ Fully backward compatible
- ✅ No API changes

## 🐛 Known Issues

None - all tests passing.

## 📚 Documentation

- **Refactoring Report:** `doc/09_report/simple_module_unfold_2026-02-04.md`
- **Release Report:** `doc/09_report/release_v0.4.0-beta.5_2026-02-04.md`
- **Refactoring Plan:** `doc/03_plan/module_refactoring_2026-02-04.md`
- **Quick Reference:** `REFACTORING.plan`

## 🚀 Getting Started

### Quick Test

```bash
# Download and test
wget -q https://github.com/ormastes/simple/releases/download/v0.4.0-beta.5/simple_runtime-bootstrap
chmod +x simple_runtime-bootstrap

# Run hello world
echo 'print "Hello from Simple v0.4.0-beta.5!"' | ./simple_runtime-bootstrap /dev/stdin
```

### Installation

```bash
# System-wide installation
sudo wget -O /usr/local/bin/simple https://github.com/ormastes/simple/releases/download/v0.4.0-beta.5/simple_runtime-bootstrap
sudo chmod +x /usr/local/bin/simple

# Verify installation
simple --version
which simple
```

## 🎯 What's Next (v0.4.0-beta.6)

Planned improvements:
- [ ] Module naming conventions (core.*, tool.* prefixes)
- [ ] Documentation updates for new structure
- [ ] Additional build optimizations
- [ ] Test coverage analysis for unfolded modules

## 🙏 Credits

- **Refactoring Pattern:** Unfold package pattern (inspired by Scala/Java package structures)
- **Build Optimization:** Rust cargo profile system
- **Module System:** Simple language native support for dot notation

---

**Full Changelog:** https://github.com/ormastes/simple/compare/v0.4.0-beta.4...v0.4.0-beta.5
