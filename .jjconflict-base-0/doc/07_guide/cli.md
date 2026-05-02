# CLI Reference

This guide covers the Simple command-line interface: arguments, subcommands, the `stats` command, and execution modes including baremetal targets.

---

## Basic Usage

```bash
simple <command> [options] [file.spl]
simple file.spl                 # Run a source file (default: run)
simple test file_spec.spl       # Run tests
simple build                    # Build the project
```

---

## Global Options

These options apply to all commands:

| Option | Short | Description |
|--------|-------|-------------|
| `--help` | `-h` | Print help and exit |
| `--version` | `-V` | Print version and exit |
| `--verbose` | `-v` | Enable verbose output |
| `--backend=NAME` | | Code generation backend (`auto`, `cranelift`, `llvm`, `llvm-lib`) |
| `--interpret` | | Force interpreter mode |
| `--no-jit` | | Disable JIT compilation |
| `--jit-threshold=N` | | JIT compilation threshold (default: 10) |
| `--gc-log` | | Enable GC logging |
| `--gc-off` | | Disable garbage collection |
| `--timeout=N` | | Timeout in seconds |
| `--max-recursion-depth=N` | | Maximum recursion depth |
| `--execution-limit=N` | | Execution step limit |

---

## Commands

### `run` (default)

Run a source file. This is the default command when a `.spl` file is given.

```bash
simple run src/main.spl
simple run src/main.spl             # Equivalent (run is default)
```

### `test`

Run tests:

```bash
simple test                         # All tests
simple test path/to/spec.spl       # Single file
simple test --list                  # List tests without running
simple test --only-slow             # Slow tests only
simple test --filter="pattern"      # Filter by name
```

### `build`

Build the project:

```bash
simple build                    # Debug build
simple build --release          # Optimized release build
simple build --target=NAME      # Build specific target
simple build --clean            # Clean build artifacts
simple build fmt                # Format code
simple build lint               # Run linter
simple build check              # All quality checks
```

### `compile`

Compile source to a standalone binary:

```bash
simple compile src/main.spl -o myprogram
simple compile src/main.spl --target=x86_64
```

### `watch`

Watch for file changes and rebuild:

```bash
simple watch                    # Watch and build
simple watch --task=test        # Watch and run tests
simple watch --debounce=1000    # Custom debounce (ms)
```

### `stats`

Display project statistics:

```bash
simple stats                    # Full statistics
simple stats --brief            # Condensed output
simple stats --quick            # Skip line counting (faster)
simple stats --json             # JSON output for CI/CD
simple stats --verbose          # Extended details
```

**Default output includes:**
- File counts by category (app, lib, std, tests)
- Lines of code
- Test pass/fail summary
- Feature completion status

**JSON output** (for CI/CD integration):

```json
{
  "files": { "total": 1144, "app": 518, "lib": 64, "std": 158, "tests": 1030 },
  "lines": { "total": 281448 },
  "tests": { "total": 27, "passed": 27, "pass_rate": 100 },
  "features": { "total": 68, "complete": 64, "in_progress": 3, "planned": 1 }
}
```

**Performance:** Full mode takes ~2-3 seconds; `--quick` takes ~0.4 seconds by skipping line counting.

### `doc-coverage`

Report documentation coverage:

```bash
simple doc-coverage                 # Terminal report
simple doc-coverage --format=md     # Markdown report
simple doc-coverage --missing       # Show undocumented items
```

### Other Commands

| Command | Description |
|---------|-------------|
| `fix file.spl --dry-run` | Preview automatic fixes |
| `todo-scan` | Update TODO tracking |
| `bug-add --id=X` | Add a bug |
| `bug-gen` | Generate bug report |
| `mcp` | Start MCP server |
| `lsp` | Start LSP server |
| `diff` | Show differences |
| `verify` | Verify project integrity |

---

## The `cli` Keyword

Simple provides a built-in `cli` keyword for declarative argument parsing in your own programs. It generates a typed struct with automatic `--help` and `--version` handling.

### Basic Example

```simple
cli Args:
    """A greeting tool"""
    -v verbose = false   """Enable verbose output"""
    -o output = ""       """Output file path"""
    name = ""            """Name to greet"""

fn main():
    val args = Args.parse()
    if args.verbose:
        print "verbose mode on"
    print "Hello, {args.name}!"
```

### Type Inference

The type of each field is inferred from its default value:

| Default | Type | CLI Behavior |
|---------|------|-------------|
| `false` | `bool` | Flag: `--verbose` sets to `true` |
| `""` | `text` | Option: `--output file.txt` |
| `0` | `i64` | Option: `--timeout 30` |
| `0.0` | `f64` | Option: `--threshold 0.5` |

### Subcommands

```simple
cli Args:
    """My Application"""
    -v verbose = false   """Verbose output"""
    default: .run

    sub run:
        """Run the application"""
        -d debug = false """Debug mode"""
    sub test:
        """Run tests"""
        -l list_only = false """List tests only"""
    sub build, clean, lint      # Pass-through subcommands

fn main():
    val args = Args.parse()
    match args.command:
        case "run":
            if args.run.debug:
                print "debug mode"
        case "test":
            run_tests(args.test.list_only)
```

### File Detection

```simple
cli Args:
    """Simple compiler"""
    file: ".spl"                # Detect .spl files as positional args
    prefetch: true              # Warm page cache for detected files
```

When a positional argument ends with the specified extension, it is captured as `args.file_path`. Remaining unmatched arguments go to `args.rest`.

### Generated API

| Function | Description |
|----------|-------------|
| `Args.parse()` | Parse arguments, exit on error |
| `Args.parse_from(argv)` | Parse from explicit argument list |
| `Args.help_text()` | Return formatted help string |

| Field | Type | Description |
|-------|------|-------------|
| `args.<option>` | Inferred | Each declared option |
| `args.command` | `text` | Active subcommand name |
| `args.file_path` | `text` | Detected file path |
| `args.rest` | `[text]` | Remaining arguments |

---

## Test Runner Environments

For baremetal and remote-interpreter work, prefer `simple test` environment
selection over raw build targets.

Use `--target=...` for compilation output. Use `simple test` environment flags
to choose where and how the test runs.

### Recommended Forms

```bash
# Local execution
bin/simple test test/my_spec.spl

# Legacy compatibility syntax still accepted for the QEMU RV32 lane
bin/simple test test/integration/baremetal/qemu_baremetal_lib_smoke_spec.spl \
  '--mode=interpreter(remote(baremetal(riscv32)))'

# Repo readiness specs for hardware-backed lanes
bin/simple test test/integration/debug/hardware/stm32wb_openocd_spec.spl
bin/simple test test/integration/debug/hardware/stm32h7_openocd_spec.spl
bin/simple test test/integration/debug/hardware/t32_native_spec.spl
bin/simple test test/integration/debug/hardware/t32_gdb_bridge_spec.spl
```

### Current Remote Matrix

| Selector | Backend | Status |
|----------|---------|--------|
| `--mode='interpreter(remote(baremetal(riscv32)))'` | QEMU RISC-V32 | Verified |
| `test/integration/debug/hardware/stm32wb_openocd_spec.spl` | STM32WB + OpenOCD | Repo-ready readiness spec |
| `test/integration/debug/hardware/stm32h7_openocd_spec.spl` | STM32H7 + OpenOCD | Repo-ready readiness spec |
| `test/integration/debug/hardware/t32_native_spec.spl` | STM32WB/STM32H7 + TRACE32 Remote API | Repo-ready readiness spec, waiting for usable TRACE32 session |
| `test/integration/debug/hardware/t32_gdb_bridge_spec.spl` | STM32WB/STM32H7 + TRACE32 GDB bridge | Repo-ready readiness spec, waiting for usable TRACE32 session |

### TRACE32 Host Helpers

The repo-managed host helpers for the T32 lanes are:

```bash
./scripts/t32_start_stm.shs stm32wb native
./scripts/t32_start_stm.shs stm32wb gdb
./scripts/t32_check_ready.shs
./scripts/t32_enable_gdb.shs localhost 20000 2331
```

See:

- `doc/07_guide/backend/trace32_linux_setup.md`
- `doc/01_research/trace32_remote_interfaces_2026-03-08.md`

---

## CI/CD Integration

### Stats-Based Health Gate

```bash
PASS_RATE=$(simple stats --json --quick | jq -r '.tests.pass_rate')
if [ "$PASS_RATE" -lt 90 ]; then
    echo "Test pass rate below 90%: $PASS_RATE%"
    exit 1
fi
```

### JSON Stats in GitHub Actions

```yaml
- name: Collect statistics
  run: bin/simple stats --json > stats.json
- name: Check pass rate
  run: cat stats.json | jq '.tests.pass_rate'
```

---

## See Also

- [Getting Started](getting_started.md) -- installation and first program
- [Build Guide](build.md) -- build system, bootstrap, and SDN configuration
- [Syntax Quick Reference](quick_reference/syntax_quick_reference.md) -- full language syntax
