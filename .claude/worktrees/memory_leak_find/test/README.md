# Simple Language Test Suite

## Directory Structure

```
test/
  unit/                    # Unit tests (single module/function)
    std/                   # Standard library tests
    lib/                   # Library tests (database, etc.)
      database/            # Database module tests
    app/                   # Application module tests
      build/               # Build system tests
      desugar/             # Desugaring tests
      io/                  # I/O module tests
      tooling/             # Test runner, linter tests
    compiler/              # Compiler unit tests (native backend)

  integration/             # Cross-module integration tests
    database_*/            # Database integration tests

  feature/                 # Feature specification tests (BDD)
    *_spec.spl             # One file per language feature

  system/                  # System-level / end-to-end tests
    features/              # Feature acceptance tests
    compiler/              # Full compilation pipeline tests

  specs/                   # Additional specification tests

  lib/                     # Import symlinks (DO NOT MODIFY)
    std/                   # -> src/lib/ (symlinks for module imports)
    app/                   # -> src/app/
    lib/                   # -> src/lib/
    compiler/              # -> src/compiler/
```

## Running Tests

```bash
# Run all tests
bin/simple test

# Run specific test file
bin/simple test path/to/spec.spl

# Run with coverage
bin/simple test --coverage

# Run with coverage threshold enforcement
SIMPLE_COVERAGE_THRESHOLD=80 bin/simple test --coverage

# List test files without running
bin/simple test --list

# Run only slow tests
bin/simple test --only-slow

# Run with fail-fast (stop on first failure)
bin/simple test --fail-fast

# Run in different modes
bin/simple test --mode=interpreter   # Default
bin/simple test --mode=smf           # SMF compiled
bin/simple test --mode=native        # Native compiled
```

## Writing Tests

Tests use the built-in SSpec BDD framework. No imports needed for `describe`, `it`, `expect`.

```simple
# test/unit/std/example_spec.spl

use std.my_module.{my_function}

describe "std.my_module":
    describe "my_function":
        it "handles normal case":
            expect(my_function(42)).to_equal(84)

        it "handles edge case":
            expect(my_function(0)).to_equal(0)
```

### Available Matchers

- `expect(x).to_equal(y)` - Exact equality
- `expect(x).to_be_nil()` - Nil check
- `expect(x).to_contain("str")` - String/array contains
- `expect(x).to_start_with("str")` - String prefix
- `expect(x).to_end_with("str")` - String suffix
- `expect(x).to_be_greater_than(y)` - Numeric comparison
- `expect(x).to_be_less_than(y)` - Numeric comparison

### Imports via Symlinks

Test files import source modules via symlinks in `test/lib/`:

```simple
# Import from src/lib/math.spl
use std.math.{sqrt, abs, pow}

# Import from src/app/build/types.spl
use app.build.types.{BuildProfile, profile_to_string}

# Import from src/lib/database/stats.spl
use lib.database.stats.{calculate_mean, calculate_std_dev}
```

If a module isn't importable, check that the symlink exists:
```bash
ls -la test/lib/std/module_name.spl
# Should point to ../../../src/lib/module_name.spl
```

## Coverage

### Running with Coverage

```bash
# Basic coverage
bin/simple test --coverage

# With threshold enforcement
SIMPLE_COVERAGE_THRESHOLD=80 bin/simple test --coverage
```

### Coverage Output

Coverage reports are generated in `.coverage/`:

| File | Description |
|------|-------------|
| `.coverage/coverage.sdn` | Raw SDN coverage data |
| `.coverage/summary.md` | Per-file coverage table |
| `.coverage/uncovered.md` | Files with <100% coverage |
| `.coverage/baseline.txt` | Previous run baseline for delta tracking |

### Coverage Threshold

Set `SIMPLE_COVERAGE_THRESHOLD` environment variable (0-100) to enforce
minimum decision coverage. The test runner exits with code 1 if coverage
falls below the threshold.

### Coverage Delta

When `--coverage` is enabled, the runner compares against the previous
baseline and reports improvements or regressions:

```
[Coverage] Delta: +5% (was 75%, now 80%)
```

## Test Categories

| Category | Directory | Purpose |
|----------|-----------|---------|
| Unit | `test/unit/` | Single module/function tests |
| Integration | `test/integration/` | Cross-module tests |
| Feature | `test/feature/` | Language feature BDD specs |
| System | `test/system/` | End-to-end pipeline tests |

## Known Limitations

Some source modules cannot be tested in the interpreter due to:

- **Generics (`<>`)**: Runtime parser fails on `<T>` syntax
- **Empty dict (`{}`)**: Parse error for empty dict literals
- **Missing FFI**: Some `extern fn` not available in runtime
- **Chained methods**: `a.b().c()` fails; use intermediate variables
- **Closure capture**: Functions cannot modify outer variables

See `MEMORY.md` for the full list of runtime limitations.

## Test Count

**Current: 480/480 files passing (0 failures)**

Run `bin/simple test --no-db --quick` for fastest execution.
