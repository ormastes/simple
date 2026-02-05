# Simple Language v0.5.0-alpha

**Alpha Release - Visibility Integration**

## What's New in 0.5.0-alpha

### Module Visibility System ✨
- `pub` and `pri` keywords for explicit visibility control
- Filename-based auto-public rules (e.g., `test_case.spl` → `TestCase` is public)
- Cross-module access validation with W0401 warnings
- HIR integration with visibility checking

### Build System Improvements
- Rust build now optional (skips silently when no rust/ directory)
- Fixed cargo_build function exports
- Silent success for pure Simple workflows

### Entry Point Consolidation  
- `bin/simple` is now the main entry point
- `bin/simple_runtime` is a compatibility symlink
- All documentation updated to use `simple` command

## Installation

```bash
tar -xzf simple-0.5.0-alpha-linux-x86_64.tar.gz
cd simple-0.5.0-alpha
export PATH="$PWD/bin:$PATH"
```

## Quick Start

```bash
# Run a Simple script
simple script.spl

# Check version
simple --version

# Run tests
simple test
```

## Package Contents

- Pre-compiled runtime binary
- Complete Simple compiler and standard library
- Documentation and examples
- Test suite

## Documentation

- User Guide: `doc/guide/`
- Language Reference: See online docs

## Support

- Issues: https://github.com/ormastes/simple/issues
- Discussions: https://github.com/ormastes/simple/discussions

---

**Note:** This is an alpha release. The visibility system is complete but may have edge cases. Please report any issues!
