# Simple Build System

The Simple language build system is fully self-hosted, implemented in Simple and configured with SDN.

## Overview

The build system is accessed through the `bin/simple` CLI:

| Command | Description |
|---------|-------------|
| `bin/simple build` | Build the project |
| `bin/simple task <task>` | Run development tasks |
| `bin/simple watch` | Watch for file changes and rebuild |

### Source Locations

| Component | Location |
|-----------|----------|
| Build system | `src/app/build/main.spl` (38 files in `src/app/build/`) |
| Task runner | `src/app/task/main.spl` |
| File watcher | `src/app/watch/main.spl` + `src/app/build/watch.spl` |
| Project config | `simple.sdn` |

## Configuration: `simple.sdn`

The project configuration is defined in SDN format:

```sdn
project:
    name: Simple
    version: 0.1.0

targets:
    formatter:
        source: src/app/formatter/main.spl
        output: bin/simple_fmt
        build_dir: build/formatter

    linter:
        source: src/app/lint/main.spl
        output: bin/simple_lint
        build_dir: build/lint

    # ... more targets
```

## Build Commands

```bash
# Build all targets
bin/simple build

# Build specific target
bin/simple build --target=formatter
bin/simple build --target=linter

# Clean build artifacts
bin/simple build --clean

# Release build
bin/simple build --release

# Verbose output
bin/simple build --verbose
```

## Task Runner

Run common development tasks:

```bash
# List all tasks
bin/simple task --list

# Run specific task
bin/simple task build
bin/simple task test
bin/simple task fmt
bin/simple task lint
bin/simple task check      # fmt + lint + test

# Quick dev cycle
bin/simple task dev        # build + test-unit

# Full CI check
bin/simple task ci         # fmt + lint + test + coverage
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
| `ci` | Full CI check | fmt, lint, test, coverage |

## Watch Mode

Automatically rebuild on file changes:

```bash
# Watch and build
bin/simple watch

# Watch and run specific task
bin/simple watch --task=test
bin/simple watch --task=fmt

# Custom debounce delay
bin/simple watch --debounce=1000  # 1 second
```

## Example Workflows

### Daily Development

```bash
# Start watch mode
bin/simple watch

# In another terminal, run tests
bin/simple test
```

### Before Commit

```bash
# Full check
bin/simple task check

# This runs:
#   1. Format all files
#   2. Lint all files
#   3. Run all tests
```

### CI Pipeline

```bash
# Full CI check
bin/simple task ci
```

### Custom Builds

```bash
# Build only formatter
bin/simple build --target=formatter

# Build formatter and linter
bin/simple build --target=formatter
bin/simple build --target=linter
```

## Build System Architecture

```
simple.sdn                        # Configuration (SDN format)
    |
src/app/build/main.spl            # Build system (Simple)
    +- Reads simple.sdn
    +- Creates build directories
    +- Compiles each target
    +- Reports results

src/app/task/main.spl             # Task runner (Simple)
    +- Defines tasks
    +- Manages dependencies
    +- Executes commands
    +- Reports status

src/app/watch/main.spl            # File watcher (Simple)
    +- Monitors file changes
    +- Debounces rapid changes
    +- Triggers rebuilds
    +- Reports events
```

### Key Features

1. **Configuration Loading** - Parse `simple.sdn` using SDN library
2. **Dependency Management** - Tasks depend on other tasks with automatic resolution
3. **Parallel Builds** - Build multiple targets in parallel
4. **Incremental Builds** - Track file modification times, only rebuild changed targets
5. **Error Handling** - Clear error messages with exit codes for CI
