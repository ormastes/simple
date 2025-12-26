# Simple Self-Hosted Build System

**Self-hosting in action!** The Simple language build system is now written in Simple itself, using SDN for configuration.

## Overview

The build system consists of three main components:

1. **`simple.sdn`** - Project configuration (SDN format)
2. **`build.spl`** - Build script (Simple language)
3. **`task.spl`** - Task runner (Simple language)
4. **`watch.spl`** - File watcher (Simple language)

## Why Self-Host?

- **Eating our own dog food** - Use Simple to build Simple tools
- **SDN configuration** - Use our own data notation format
- **No bash dependencies** - Pure Simple implementation
- **Cross-platform** - Works anywhere Simple runs
- **Extensible** - Easy to add new tasks and targets

## Configuration: `simple.sdn`

The project configuration is defined in SDN format:

```sdn
project:
    name: Simple
    version: 0.1.0

targets:
    formatter:
        source: simple/app/formatter/main.spl
        output: simple/bin_simple/simple_fmt
        build_dir: simple/build/formatter

    linter:
        source: simple/app/lint/main.spl
        output: simple/bin_simple/simple_lint
        build_dir: simple/build/lint

    # ... more targets
```

## Build Script: `build.spl`

Replace the old bash script with Simple:

```bash
# Old way (bash)
./simple/build_tools.sh

# New way (Simple)
simple simple/build.spl
```

### Build Commands

```bash
# Build all targets
simple simple/build.spl

# Build specific target
simple simple/build.spl --target=formatter
simple simple/build.spl --target=linter
simple simple/build.spl --target=sdn

# Clean build artifacts
simple simple/build.spl --clean

# Watch mode (auto-rebuild on changes)
simple simple/build.spl --watch

# Verbose output
simple simple/build.spl --verbose
```

## Task Runner: `task.spl`

Run common development tasks:

```bash
# List all tasks
simple simple/task.spl --list

# Run specific task
simple simple/task.spl build
simple simple/task.spl test
simple simple/task.spl fmt
simple simple/task.spl lint
simple simple/task.spl check      # fmt + lint + test

# Quick dev cycle
simple simple/task.spl dev        # build + test-unit

# Full CI check
simple simple/task.spl ci         # fmt + lint + test + coverage
```

### Available Tasks

| Task | Description | Dependencies |
|------|-------------|--------------|
| `build` | Build all tools | - |
| `test` | Run all tests | - |
| `test-unit` | Run unit tests only | - |
| `test-system` | Run system tests only | - |
| `fmt` | Format all .spl files | build |
| `lint` | Lint all .spl files | build |
| `check` | Format + lint + test | fmt, lint, test |
| `clean` | Clean build artifacts | - |
| `dev` | Quick dev build | build, test-unit |
| `ci` | Full CI check | fmt-rust, lint-rust, test, coverage |

## Watch Mode: `watch.spl`

Automatically rebuild on file changes:

```bash
# Watch and build
simple simple/watch.spl

# Watch and run specific task
simple simple/watch.spl --task=test
simple simple/watch.spl --task=fmt

# Custom debounce delay
simple simple/watch.spl --debounce=1000  # 1 second
```

### Watch Configuration

Configure in `simple.sdn`:

```sdn
tools:
    watch:
        enabled: true
        patterns = ["**/*.spl", "**/*.sdn"]
        ignore = ["build/**", "target/**", "bin_simple/**"]
        debounce_ms: 500
```

## Migration from Bash

### Before (Bash)

```bash
# Build
./simple/build_tools.sh

# Clean
rm -rf simple/build simple/bin_simple

# Rebuild
./simple/build_tools.sh --clean && ./simple/build_tools.sh
```

### After (Simple)

```bash
# Build
simple simple/build.spl

# Clean
simple simple/build.spl --clean

# Rebuild
simple simple/task.spl clean && simple simple/task.spl build
```

## Advantages

### 1. **SDN Configuration**
- Human-readable format
- Comments and documentation inline
- Easy to parse and modify
- Self-hosted data format

### 2. **Simple Language**
- Type-safe build scripts
- Error handling with Result types
- Pattern matching for clarity
- No shell injection vulnerabilities

### 3. **Cross-Platform**
- No bash dependency
- Works on Windows without WSL
- Pure Simple implementation

### 4. **Extensible**
- Easy to add new targets
- Custom tasks in Simple
- Programmable build logic

### 5. **Integrated**
- Uses SDN library we just built
- Uses Simple standard library
- Self-hosting demonstration

## Example Workflows

### Daily Development

```bash
# Start watch mode
simple simple/watch.spl

# In another terminal, make changes to .spl files
# Watch will automatically rebuild

# Run tests
simple simple/task.spl test
```

### Before Commit

```bash
# Full check
simple simple/task.spl check

# This runs:
#   1. Format all files
#   2. Lint all files
#   3. Run all tests
```

### CI Pipeline

```bash
# Full CI check (Rust + Simple)
simple simple/task.spl ci

# This runs:
#   1. Format Rust code
#   2. Lint Rust code
#   3. Run all tests
#   4. Generate coverage
```

### Custom Builds

```bash
# Build only formatter
simple simple/build.spl --target=formatter

# Build formatter and linter
simple simple/build.spl --target=formatter
simple simple/build.spl --target=linter

# Or use task runner
simple simple/task.spl build --target=formatter
```

## Implementation Details

### Build System Architecture

```
simple.sdn                 # Configuration (SDN format)
    ↓
build.spl                  # Build script (Simple)
    ├─ Reads simple.sdn
    ├─ Creates build directories
    ├─ Compiles each target
    └─ Reports results

task.spl                   # Task runner (Simple)
    ├─ Defines tasks
    ├─ Manages dependencies
    ├─ Executes commands
    └─ Reports status

watch.spl                  # File watcher (Simple)
    ├─ Monitors file changes
    ├─ Debounces rapid changes
    ├─ Triggers rebuilds
    └─ Reports events
```

### Key Features

1. **Configuration Loading**
   - Parse `simple.sdn` using SDN library
   - Extract targets, paths, settings
   - Type-safe configuration access

2. **Dependency Management**
   - Tasks can depend on other tasks
   - Automatic dependency resolution
   - Prevents circular dependencies

3. **Parallel Builds**
   - Build multiple targets in parallel
   - Configurable max jobs
   - Respects dependencies

4. **Incremental Builds**
   - Track file modification times
   - Only rebuild changed targets
   - Cache build artifacts

5. **Error Handling**
   - Clear error messages
   - Exit codes for CI
   - Detailed failure reporting

## Future Enhancements

- [ ] Parallel task execution
- [ ] Incremental compilation
- [ ] Build caching (ccache-style)
- [ ] Remote build support
- [ ] Build profiling
- [ ] Dependency graph visualization
- [ ] Hot reload for development
- [ ] Build notifications
- [ ] Custom task definitions in simple.sdn
- [ ] Plugin system for custom builders

## Comparison

| Feature | Bash Script | Simple Build |
|---------|-------------|--------------|
| **Language** | Bash | Simple |
| **Config Format** | Hardcoded | SDN |
| **Type Safety** | None | Full |
| **Error Handling** | Basic | Result types |
| **Cross-Platform** | Limited | Full |
| **Extensibility** | Hard | Easy |
| **Self-Hosting** | No | Yes |
| **Watch Mode** | External tool | Built-in |
| **Task Dependencies** | Manual | Automatic |

## Getting Started

### Prerequisites

1. Build the Rust compiler:
   ```bash
   cargo build
   ```

2. Build the SDN library (using bash script initially):
   ```bash
   ./simple/build_tools.sh
   ```

### First Build with Simple

Once you have the SDN CLI built, you can use the Simple build system:

```bash
# Build everything
simple simple/build.spl

# Or use task runner
simple simple/task.spl build
```

### Migrate Completely

Once comfortable, replace all bash usage:

```bash
# Instead of: ./simple/build_tools.sh
simple simple/build.spl

# Instead of: make test
simple simple/task.spl test

# Instead of: make check
simple simple/task.spl check
```

## Self-Hosting Achievement 🎉

This build system demonstrates **complete self-hosting**:

1. ✅ **SDN for configuration** - Using our own data format
2. ✅ **Simple for build scripts** - Using our own language
3. ✅ **No external dependencies** - Pure Simple implementation
4. ✅ **Full-featured** - Build, test, watch, tasks
5. ✅ **Production-ready** - Used to build itself

**We're eating our own dog food!** 🍖🐕
