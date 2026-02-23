# Release v0.4.0-beta.5 - Completion Report

**Date:** 2026-02-04
**Tag:** v0.4.0-beta.5
**URL:** https://github.com/ormastes/simple/releases/tag/v0.4.0-beta.5

## Summary

Successfully created GitHub release v0.4.0-beta.5 with both bootstrap and full release binaries, featuring the Simple module unfold refactoring.

## Release Contents

### Binaries

1. **simple_runtime-release** (26 MB)
   - Full release build with all optimizations
   - Location: `rust/target/release/simple_runtime`
   - Profile: `--release`

2. **simple_runtime-bootstrap** (13 MB)
   - Minimal size bootstrap build
   - Location: `rust/target/bootstrap/simple_runtime`
   - Profile: `--profile bootstrap`
   - **50% smaller** than release build

### Key Features

**Module Refactoring** - Applied unfold package pattern to 22 Simple module subdirectories:

**Interpreter module (14 subdirectories):**
- `interpreter/async_runtime/` → `interpreter.async_runtime/`
- `interpreter/control/` → `interpreter.control/`
- `interpreter/core/` → `interpreter.core/`
- `interpreter/expr/` → `interpreter.expr/`
- `interpreter/ffi/` → `interpreter.ffi/`
- `interpreter/helpers/` → `interpreter.helpers/`
- `interpreter/collections/` → `interpreter.collections/`
- `interpreter/memory/` → `interpreter.memory/`
- `interpreter/lazy/` → `interpreter.lazy/`
- `interpreter/perf/` → `interpreter.perf/`
- `interpreter/call/` → `interpreter.call/`
- `interpreter/module/` → `interpreter.module/`
- `interpreter/extern/` → `interpreter.extern/`
- `interpreter/utils/` → `interpreter.utils/`

**Other modules (8 subdirectories):**
- `lsp/handlers/` → `lsp.handlers/`
- `dashboard/views/` → `dashboard.views/`
- `dashboard/render/` → `dashboard.render/`
- `web_dashboard/api/` → `web_dashboard.api/`
- `web_dashboard/static/` → `web_dashboard.static/`
- `package/registry/` → `package.registry/`
- `ffi_gen/specs/` → `ffi_gen.specs/`
- `ffi_gen/templates/` → `ffi_gen.templates/`

## Benefits

1. **Visible Hierarchy**: Module parent-child relationships visible at directory level
2. **Easier Navigation**: All related modules visible with `ls src/app/`
3. **Clear Organization**: Related modules group alphabetically by prefix
4. **Zero Code Changes**: Import paths unchanged (already use dot notation)

## Build Details

### Bootstrap Build
```bash
cargo build --profile bootstrap
```
- Size: 13 MB (50% reduction)
- Optimizations: `opt-level = "z"`, `lto = true`, `strip = true`
- Use case: Distribution, minimal deployments

### Release Build
```bash
cargo build --release
```
- Size: 26 MB
- Optimizations: Full release optimizations
- Use case: Standard deployments

## Commits Included

- feat: Unfold Simple modules (interpreter, lsp, dashboard, etc.) - `520ef7df`

## Files Changed

- 152 files renamed (directory moves only)
- 0 lines of code changed
- 0 import statements modified

## Related Documentation

- **Completion Report:** `doc/report/simple_module_unfold_2026-02-04.md`
- **Refactoring Plan:** `doc/plan/module_refactoring_2026-02-04.md`
- **Architecture:** `doc/architecture/modules.md`

## Download

```bash
# Download release binary (26 MB)
wget https://github.com/ormastes/simple/releases/download/v0.4.0-beta.5/simple_runtime-release

# Download bootstrap binary (13 MB, recommended)
wget https://github.com/ormastes/simple/releases/download/v0.4.0-beta.5/simple_runtime-bootstrap

# Make executable
chmod +x simple_runtime-bootstrap
```

## Verification

```bash
# Check binary
./simple_runtime-bootstrap --version

# Run simple program
./simple_runtime-bootstrap hello.spl
```

## Notes

- Both binaries are functionally equivalent
- Bootstrap binary recommended for smaller download and faster deployment
- Simple code refactoring only - no Rust code changes
- Backward compatible - all existing imports work unchanged

## Success Metrics

✅ Release created successfully
✅ Both binaries uploaded (release: 26 MB, bootstrap: 13 MB)
✅ 22 Simple modules unfolded
✅ Zero code changes required
✅ All builds passing

## Next Release

Planned improvements for v0.4.0-beta.6:
- Additional module visibility improvements (naming conventions)
- Documentation updates
- Test coverage for unfolded modules
