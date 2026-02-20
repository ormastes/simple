# Test Writing Skill

## Critical Rules

**NEVER ignore tests without explicit user approval:**
- Do NOT comment out test code
- Do NOT skip failing tests as a "fix"
- ALWAYS fix root cause or ask user

## Running Tests

```bash
bin/simple test                          # All tests
bin/simple test path/to/spec.spl         # Single test file
bin/simple test --list                   # List tests without running
bin/simple test --only-slow              # Run slow tests
bin/simple test --tag=integration        # Filter by tag
```

## Container Testing (Safe / Isolated)

Prefer container testing to avoid side effects on the host environment.

```bash
# Build image (once)
docker build -t simple-test-isolation:latest -f tools/docker/Dockerfile.test-isolation .

# Run tests in container (read-only workspace mount)
docker run --rm -v $(pwd):/workspace:ro --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test                   # All tests
docker run --rm -v $(pwd):/workspace:ro --memory=512m --cpus=1.0 \
  simple-test-isolation:latest test test/unit/        # Unit tests only

# Docker Compose (easiest for local development)
docker-compose -f config/docker-compose.yml up unit-tests         # Unit tests
docker-compose -f config/docker-compose.yml up integration-tests  # Integration tests
docker-compose -f config/docker-compose.yml up system-tests       # System tests
docker-compose -f config/docker-compose.yml up all-tests          # All tests parallel
docker-compose -f config/docker-compose.yml run dev-shell         # Interactive shell

# Helper scripts
scripts/local-container-test.sh unit                       # Unit tests in container
scripts/local-container-test.sh quick path/to/spec.spl    # Single test
scripts/local-container-test.sh shell                      # Interactive debugging
scripts/ci-test.sh                                         # CI-style execution
```

### Container Testing Troubleshooting

**Container not found:** `docker build -t simple-test-isolation:latest -f tools/docker/Dockerfile.test-isolation .`
**Permission denied:** `chmod +x bin/release/simple` or `sudo usermod -aG docker $USER && newgrp docker`
**Out of memory:** Increase `--memory=512m` to `--memory=1g` or `--memory=2g`
**Timeout errors:** Use correct profile: `--profile=slow` (10 min) or `--profile=intensive` (30 min)
**Tests pass locally, fail in CI:** Run exact CI command: `scripts/ci-test.sh test/unit/`

**Volume mount not working (Windows):**
- PowerShell: `docker run -v ${PWD}:/workspace:ro ...`
- CMD: `docker run -v %cd%:/workspace:ro ...`

**Container build fails:**
- Check runtime exists: `ls -lh bin/release/simple` (should be ~33MB)
- If missing: `scripts/install.sh` or download from releases

**jq not installed (parse errors):**
- Ubuntu: `sudo apt install jq`
- macOS: `brew install jq`

**Docker daemon not running:**
- Linux: `sudo systemctl start docker`
- macOS/Windows: Start Docker Desktop

```bash
# Docker Compose cleanup
docker-compose -f config/docker-compose.yml run dev-shell
# Inside: simple test test/unit/failing_spec.spl --verbose
docker-compose build --no-cache     # Rebuild after Dockerfile changes
docker-compose down                 # Stop services
docker system prune -a              # Remove all containers/images
```

**Full Guide:** `doc/guide/container_testing.md` | **Resource Limits:** `doc/guide/resource_limits.md` | **Test Config:** `simple.test.sdn`

## Writing Simple BDD Tests

Tests go in `test/` directory. Use `*_spec.spl` naming.

**CRITICAL: Use docstring markdown, NOT println() for test documentation!**

```simple
# feature_spec.spl

describe "Feature":
    """
    # Feature Module

    Provides core functionality for X, Y, Z.

    ## Overview
    - Feature A does X
    - Feature B does Y

    ## Usage
    ```simple
    val f = Feature(value: 10)
    f.increment()
    ```
    """

    context "when initialized":
        """
        Tests default initialization behavior.
        Ensures all fields start with correct values.
        """

        it "should have default value":
            """
            Default constructor should initialize value to 0.

            **Expected:** value = 0
            **Actual:** Verified via expect() assertion
            """
            val f = Feature(value: 0)
            expect(f.value).to_equal(0)

    context "with operations":
        """
        Tests arithmetic operations on Feature.

        ## Tested Operations
        - increment(): adds 1
        - decrement(): subtracts 1
        - add(n): adds n
        """

        it "should increment":
            """
            Increment operation should add 1 to current value.

            Given: Feature with value 10
            When: increment() is called
            Then: value should be 11
            """
            val f = Feature(value: 10)
            f.increment()
            expect(f.value).to_equal(11)
```

**Documentation Guidelines:**
- **Every `describe` block**: Rich markdown overview with usage examples
- **Every `context` block**: Explain what scenario/condition is being tested
- **Every `it` block**: Document expected behavior, inputs, outputs
- **Use markdown**: Headers, lists, code blocks, tables
- **NO println()**: All explanations go in docstrings, not print statements
- **Auto-generate docs**: SSpec uses docstrings for spec documentation

## Test File Naming

- Simple: `*_spec.spl` or `*_test.spl`
- Tests directory: `test/`
- Feature specs: `src/lib/test/features/`

## Test Types

| Type | Syntax | Behavior |
|------|--------|----------|
| Regular | `it "..."` | Runs by default |
| Slow | `slow_it "..."` | Auto-ignored, run with `--only-slow` |
| Skipped | `skip("name", "reason")` | Not yet implemented |

## Matchers Reference

Built-in runtime matchers only:

| Matcher | Usage |
|---------|-------|
| `to_equal(val)` | `expect(x).to_equal(5)` |
| `to_be(val)` | `expect(x).to_be(5)` |
| `to_be_nil()` | `expect(x).to_be_nil()` |
| `to_contain(item)` | `expect(list).to_contain(5)` |
| `to_start_with(s)` | `expect(text).to_start_with("he")` |
| `to_end_with(s)` | `expect(text).to_end_with("lo")` |
| `to_be_greater_than(n)` | `expect(x).to_be_greater_than(5)` |
| `to_be_less_than(n)` | `expect(x).to_be_less_than(10)` |

**Note:** `to_be_true`/`to_be_false` are NOT built-in. Use `to_equal(true)` / `to_equal(false)` instead.

## Run Tracking

Test results are automatically tracked in `doc/test/test_db.sdn`.

```bash
bin/simple test --list-runs              # View run history
bin/simple test --cleanup-runs           # Clean stale runs
bin/simple test --prune-runs=50          # Keep 50 most recent
```

Reports are generated at `doc/test/test_result.md` after every test run.

## See Also

- `/sspec` skill - Full SSpec BDD framework details
- `.claude/templates/sspec_template.spl` - Template for new specs
- `doc/guide/sspec_complete_example.md` - Complete workflow example
- `doc/spec/testing/` - Testing framework specs
