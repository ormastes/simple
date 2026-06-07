# Simple Language Test Suite

## Directory Structure

```
test/
  unit/                    # Unit tests for one module/function/model
  integration/             # Cross-module host-runner workflows
  feature/                 # User-visible feature and compatibility specs
  system/                  # End-to-end, QEMU, OS, hardware-gated specs
  shared/                  # Import-free cross-platform specs
  fixtures/                # Helper modules, scripts, generated inputs
  baselines/               # Goldens and expected outputs
  perf/                    # Benchmark and performance checks
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

The executable tree is also the source of truth for generated scenario
documentation. After removing the leading `test/` segment, generated SPipe docs
must mirror the same path below `doc/06_spec/`. Example:
`test/03_system/feature/usage/math_blocks_spec.spl` generates
`doc/06_spec/feature/usage/math_blocks_spec.md`.

Generated SSpec manuals should read as scenario-based manuals, not as raw test dumps.
For feature, system, app, MCP, UI, protocol, hardware, and environmental tests,
write helper/checker functions so the generated manual can show ordered user or
operator steps, typed capture evidence, and folded executable SSpec details.
Use `doc/07_guide/infra/sspec_scenario_manual.md` when deciding whether a
scenario should be visible, folded as advanced/edge detail, or skipped from the
manual while remaining executable.

`bin/simple test` now prefers fresh local driver builds from
`src/compiler_rust/target/bootstrap`, `target/release`, and `target/debug`
before older packaged binaries in `bin/release/`. That keeps focused test runs
aligned with the current workspace compiler/runtime changes.

## Writing Tests

Tests use the built-in SSpec BDD framework. Unit-style specs can import
`use std.spec` for `describe`, `it`, and `expect`. SSpec scenario manuals should
prefer `use std.spec.*` so the `step("...")` manual helper is visible next to
the BDD surface. SPipe is the runner/docgen process around these `.spl` specs.

```simple
# test/01_unit/std/example_spec.spl

use std.spec
use std.my_module.{my_function}

describe "std.my_module":
    describe "my_function":
        it "handles normal case":
            expect(my_function(42)).to_equal(84)

        it "handles edge case":
            expect(my_function(0)).to_equal(0)
```

### Scenario Manual Quality

When a spec describes user-visible, operator-visible, system, protocol, MCP, or
environmental behavior, author it as an executable scenario manual:

- Put primary flows in normal `it` scenarios with explicit `step("...")`
  action text.
- Use `# @inline` for reusable setup scenarios and `# @include("...")` to
  expand them into the visible scenario where those steps belong.
- Treat `Given_*`, `When_*`, and `Then_*` helper naming as legacy style. Keep it
  only when maintaining older specs; use `step("...")` for new scenario
  manuals.
- Use `@step` metadata only for older helper/checker functions when the
  fallback function name would not read like a manual sentence.
- Use `# @prev("...")` when the visible scenario should start with a previous
  setup scenario.
- Use `@capture` only where manual evidence is useful. Capture is off by
  default; bare `@capture` means after-step capture with default kind `tui`.
- Use typed capture kinds for non-UI evidence: `api`, `protocol`, `exec`,
  `binary`, `html`, `text`, `log`, or `artifact`.
- For Simple Web or other HTML-backed GUI surfaces, prefer HTML/visible-text
  capture and checks; keep screenshot GUI capture as fallback evidence.
- Use `# @evidence-display: embed_tui`, `links`, or `embed_all` when the
  generated manual needs a different evidence display policy. The default is
  embedded TUI captures and linked non-TUI artifacts.
- Fold or skip very detailed edge, matrix, stress, generated, and helper-only
  scenarios with manual visibility policy instead of forcing them into the main
  manual.

Primary scenario-manual example:

```simple
use std.spec.*

describe "Dashboard actions":
    # @inline
    it "operator has an authenticated session":
        step("Open the sign-in page")
        step("Submit valid credentials")

    it "operator reviews dashboard actions":
        # @include("operator has an authenticated session")
        step("Open the actions panel")
        expect("actions").to_equal("actions")
```

After writing or changing such a spec, generate the doc and read it like a
hand-written manual. If it still reads like test plumbing, improve the steps,
captures, visibility, or helper/checker names before calling the spec done.

### Available Matchers

- `expect(condition)` - Boolean true assertion
- `expect_not(condition)` - Boolean false assertion
- `expect(x).to_equal(y)` - Exact equality
- `expect(x).to_be_nil()` - Nil check
- `expect(x).to_contain("str")` - String/array contains
- `expect(x).to_start_with("str")` - String prefix
- `expect(x).to_end_with("str")` - String suffix
- `expect(x).to_be_greater_than(y)` - Numeric comparison
- `expect(x).to_be_less_than(y)` - Numeric comparison

Use bare `expect(condition)` for true boolean checks and `expect_not(condition)`
for false boolean checks. SPipe quality lint warns on verbose
`expect(condition).to_equal(true)` and denies false boolean wrappers such as
`expect(condition).to_equal(false)`.

### Imports via Symlinks

Test files import source modules from the canonical test trees:

```simple
# Import from src/lib/math.spl
use std.math.{sqrt, abs, pow}

# Import from src/app/build/types.spl
use app.build.types.{BuildProfile, profile_to_string}

# Import from src/lib/database/stats.spl
use lib.database.stats.{calculate_mean, calculate_std_dev}
```

If a module isn't importable, check that the source module exists:
```bash
ls -la src/lib/module_name.spl
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
| Unit | `test/01_unit/` | Single module/function tests |
| Shared | `test/shared/` | Import-free cross-platform specs marked `# @platform: all` |
| Integration | `test/integration/` | Cross-module tests |
| Feature | `test/03_system/feature/` | Language feature BDD specs |
| System | `test/03_system/` | End-to-end pipeline tests |

## Traceability Rules

- Keep one scenario source per behavior-oriented `*_spec.spl` file.
- Put unit tests under `test/01_unit/<source-area>/...`.
- Put import-free cross-platform specs under `test/shared/<domain>/...`; shared specs may use built-in `describe`/`context`/`it`/`expect` only.
- Put cross-module tests under `test/integration/<source-area>/...`.
- Put user-visible feature BDD tests under `test/03_system/feature/<domain>/...`.
- Put end-to-end workflows under `test/03_system/<domain>/...`.
- Generated manual/spec docs live at the matching `doc/06_spec/<same path>.md`.
- Generated manual/spec docs for scenario-oriented files must be reviewed as
  scenario manuals: primary scenarios visible, advanced/edge details folded or
  skipped by policy, captures attached to the step that caused them, and
  executable code available as folded detail.
- Requirement, research, design, plan, implementation, guide, and generated spec
  links should use the same feature slug so traceability scans can match them.
- Treat older executable top-level suites outside `unit/`, `shared/`,
  `integration/`, `feature/`, and `system/` as transitional unless maintaining
  an existing suite in place. Do not add a new top-level test category without
  documenting why it cannot fit the canonical buckets.
- Keep support assets such as baselines, fixtures, generated data, and helper
  modules separate from executable scenario placement decisions.
- See `doc/07_guide/testing/test_layout_traceability.md` for the move
  checklist and current canonical-root policy.
- See `doc/07_guide/infra/sspec_scenario_manual.md` for scenario manual,
  inline/previous scenario, capture, and environmental-test guidance.

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
