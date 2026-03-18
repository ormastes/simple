---
name: test
description: SSpec BDD testing framework, matchers, fixtures, coverage measurement, and container testing
---

# Test & SSpec Skill

SSpec is Simple's BDD testing framework that generates documentation from tests.

## Critical Rules

- NEVER add `#[ignore]` without user approval
- NEVER skip failing tests as a "fix"
- NEVER comment out test code
- ALWAYS fix root cause or ask user
- One assertion concept per test
- Clear test names: `it "adds two positive numbers":` not `it "works":`

## Quick Start

`describe`, `it`, and `expect` are **built-in** to the runtime -- no import needed.

```simple
describe "Calculator":
    context "addition":
        it "adds two numbers":
            expect(2 + 2).to_equal(4)
```

Run: `bin/simple test` or `bin/simple test path/to/spec.spl`

## Running Tests

```bash
# All tests
bin/simple test

# Specific file
bin/simple test test/my_feature_spec.spl

# List tests without running
bin/simple test --list

# Filter by tag
bin/simple test --tag=integration

# Run only slow tests
bin/simple test --only-slow

# Match by name
bin/simple test --match "Stack when empty"

# Fail fast
bin/simple test --fail-fast

# Run tracking
bin/simple test --list-runs
bin/simple test --cleanup-runs
bin/simple test --prune-runs=50
```

Reports are generated at `doc/test/test_result.md` after every test run.

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

**Full Guide:** `doc/guide/testing/container_testing.md` | **Test Config:** `simple.test.sdn`

## Built-in Matchers Reference

The runtime provides these matchers on `expect(value)`:

| Matcher | Usage | Description |
|---------|-------|-------------|
| `.to_equal(expected)` | `expect(x).to_equal(42)` | Equality check |
| `.to_be(expected)` | `expect(x).to_be(42)` | Identity/equality check |
| `.to_be_nil` | `expect(x).to_be_nil` | Nil check |
| `.to_contain(item)` | `expect(list).to_contain(3)` | Collection/string contains |
| `.to_start_with(prefix)` | `expect(s).to_start_with("he")` | String prefix |
| `.to_end_with(suffix)` | `expect(s).to_end_with("lo")` | String suffix |
| `.to_be_greater_than(n)` | `expect(10).to_be_greater_than(5)` | Numeric comparison |
| `.to_be_less_than(n)` | `expect(5).to_be_less_than(10)` | Numeric comparison |

**Important:** Use `.to_equal()` style, NOT `.to(eq())` style. The runtime does not support the `to(matcher())` pattern.

**Boolean checks:** Use `.to_equal(true)` and `.to_equal(false)` -- there are no `.to_be_true()` or `.to_be_false()` matchers.

## Test Types

| Type | Keyword | Behavior |
|------|---------|----------|
| Regular | `it "..."` | Runs by default |
| Slow | `slow_it "..."` | Auto-ignored, run with `--only-slow` |
| Skipped | `skip_it "..."` | Skipped in interpreter, runs in compiled mode |
| Pending | `pending "reason"` | Marked as pending |

## BDD Syntax

### Groups & Tests

```simple
describe "Feature":
    """Optional docstring for generated docs."""

    context "when empty":
        it "returns zero":
            expect([].len()).to_equal(0)

    context "when populated":
        it "has items":
            expect([1, 2, 3].len()).to_equal(3)
```

### Hooks

| Hook | Scope | Order |
|------|-------|-------|
| `before_each:` | per test | outer -> inner |
| `after_each:` | per test | inner -> outer |

```simple
context "with setup":
    before_each:
        setup()
    after_each:
        cleanup()
    it "test":
        expect(true).to_equal(true)
```

### Fixtures

```simple
# Lazy (memoized per test)
given_lazy :user, \:
    { name: "Alice" }

# Eager setup
given:
    setup_db()

# Named eager
given :db_connect, \:
    database.connect()
```

### Shared Contexts

```simple
context_def :as_admin:
    given_lazy :user, \:
        create(:user, :admin)

describe "Dashboard":
    context :as_admin:
        it "shows admin panel":
            expect(user.admin).to_equal(true)
```

## Complete Workflow: Test -> Documentation

### 1. Create Spec File from Template

```bash
# Copy template to your feature directory
cp .claude/templates/sspec_template.spl test/my_feature_spec.spl
```

### 2. Write Module-Level Documentation

**REQUIRED format** at the top of every spec file:

```simple
"""
# Feature Name Specification

**Feature IDs:** #100-110
**Category:** Language | Syntax | Stdlib | Runtime | Testing | Tooling
**Difficulty:** 1-5/5
**Status:** Draft | In Progress | Implemented | Complete

## Overview

High-level description of what this feature does and why it exists.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Term1   | Definition |

## Related Specifications

- [Types](types.md) - Related spec
- [Memory](memory.md) - Related spec

## Examples

Basic usage examples.
"""
```

**Metadata Fields:**

| Field | Required | Values | Purpose |
|-------|----------|--------|---------|
| Feature IDs | Yes | `#100-110` | Tracking & cross-reference |
| Category | Yes | `Infrastructure`, `Language`, `Syntax`, `Stdlib`, `Runtime`, `Testing`, `Tooling` | Index organization |
| Difficulty | No | `1-5/5` | Complexity indicator |
| Status | Yes | `Draft`, `In Progress`, `Implemented`, `Complete` | Development stage |
| Requirements | Recommended | `doc/requirement/xxx.md` | Link to requirement document |
| Plan | Recommended | `doc/plan/xxx.md` | Link to plan document |
| Design | Recommended | `doc/design/xxx.md` | Link to design/architecture document |
| Research | Recommended | `doc/research/xxx.md` | Link to research document |

**Doc-link validation:** `sspec-docgen` performs two checks for each link field:
1. **Missing** -- field absent -> warning with recommended path
2. **Not found** -- field set but file doesn't exist -> warning with exact path

Use `N/A` to suppress a warning when the link is genuinely not applicable:
```
**Requirements:** N/A
```

### 3. Write Tests with Documentation

**CRITICAL: Use docstring markdown, NOT println() for test documentation!**

```simple
# No import needed -- describe/it/expect are built-in

describe "MyFeature":
    """
    ## Basic Usage

    Description of test group.
    """

    context "when condition":
        """
        ### Scenario: Specific Case

        Detailed scenario description.
        """

        it "does expected behavior":
            """
            Default constructor should initialize value to 0.

            **Expected:** value = 0
            **Actual:** Verified via expect() assertion
            """
            expect(actual).to_equal(expected)
```

**Documentation Guidelines:**
- **Every `describe` block**: Rich markdown overview with usage examples
- **Every `context` block**: Explain what scenario/condition is being tested
- **Every `it` block**: Document expected behavior, inputs, outputs
- **Use markdown**: Headers, lists, code blocks, tables
- **NO println()**: All explanations go in docstrings, not print statements
- **Auto-generate docs**: SSpec uses docstrings for spec documentation

### 4. Run Tests

```bash
bin/simple test test/my_feature_spec.spl
```

### 5. Generate Documentation

```bash
# Generate docs for feature specs
bin/simple doc-gen

# Output: doc/spec/language/
```

### 6. Review Generated Docs

```bash
# View generated docs
cat doc/spec/language/README.md
cat doc/spec/language/my_feature_spec.md
```

The generator:
- Extracts `"""..."""` docstrings as markdown
- Preserves all markdown formatting (tables, code blocks, lists)
- Adds metadata (Feature IDs, source file, timestamp)
- Creates navigable index by category
- Validates completeness and warns about issues

### Making Links

Standard markdown link syntax works inside docstrings:

```simple
"""
## Links in Documentation

### Internal Links (relative)
- [Types Specification](types.md)
- [Functions](functions.md#pattern-matching)
- [See Overview](#overview)

### External Links
- [Simple Language](https://github.com/org/simple)

### Anchor Links
Use `{#anchor-name}` for custom anchors:

## Section Name {#custom-anchor}

Then link: [Go to section](#custom-anchor)
"""
```

### Generated Output Location

```
doc/spec/language/
  README.md           # Index with links to all specs
  syntax.md           # Generated from syntax_spec.spl
  types.md            # Generated from types_spec.spl
  ...
```

### Generated README Structure

The generator creates an index with:
- Quick navigation by category
- Links to each spec: `[Syntax Specification](syntax.md)`
- Status badges, test counts, feature IDs
- Symbol references with anchor links

## Test File Structure

### Location
```
test/
  lib/           # Library tests
  compiler/      # Compiler tests
  app/           # Application tests
src/lib/test/
  unit/          # Fast, isolated (branch/condition coverage)
  integration/   # Public function touch (100%)
  system/        # Public type touch (100%)
```

### Naming
- Files: `*_spec.spl` or `*_test.spl`
- Describe: `describe "ClassName":`
- Context: `context "when condition":`
- Test: `it "does something":`

## Coverage Measurement

```bash
# Generate coverage
bin/simple build coverage

# Coverage data location: .coverage/coverage.sdn
```

## Lean Verification Integration

SSpec tests can reference formal verification in docstrings:

```simple
"""
### Lean Verification

This feature is verified in:
- `verification/TypeInference.lean` - Soundness proof
- `verification/MixinSubstitution.lean` - Type safety

**Properties Verified:**
1. Type substitution preserves well-typedness
2. Mixin application is associative

See [architecture skill](/architecture) for verification workflow.
"""
```

Generate Lean from verified code:
```bash
bin/simple gen-lean compare           # Check alignment
bin/simple gen-lean write --force     # Regenerate Lean files
```

## Quick Reference

### Starting a New Spec

1. **Copy template:**
   ```bash
   cp .claude/templates/sspec_template.spl test/my_feature_spec.spl
   ```

2. **Fill in required metadata:**
   - Feature IDs
   - Category
   - Status
   - Overview

3. **Write tests with docstrings**

4. **Run tests:**
   ```bash
   bin/simple test test/my_feature_spec.spl
   ```

5. **Generate docs:**
   ```bash
   bin/simple doc-gen
   ```

### Common Mistakes to Avoid

- **Don't:** Skip module-level docstring -- Generator will warn "No documentation"
- **Do:** Always start with `"""# Feature Name Specification..."""`

- **Don't:** Use single-line `#` comments for docs -- Not extracted
- **Do:** Use triple-quoted `"""..."""` docstrings

- **Don't:** Use `.to(eq(...))` matcher style -- Not supported
- **Do:** Use `.to_equal(...)` directly on the expect result

- **Don't:** Use `.to_be_true()` or `.to_be_false()` -- Not in built-in matchers
- **Do:** Use `.to_equal(true)` and `.to_equal(false)`

- **Don't:** Mix test code with helpers -- Hard to read
- **Do:** Put helpers at the end under `# Helper Code` comment

- **Don't:** Write specs without running tests -- May have syntax errors
- **Do:** Test -> Document -> Generate workflow

## See Also

- **[Template](../../.claude/templates/sspec_template.spl)** - Spec file template
- `doc/spec/sspec_format.md` - Format details
- `doc/guide/testing/testing.md` - Testing guide (includes SSpec)
- `doc/guide/testing/container_testing.md` - Container testing guide
- `doc/spec/sspec_manual.md` - User manual
- `doc/test.md` - Test policy
- `doc/FILE.md` - Document relationship model (PLAN -> REQ -> FEATURE -> TESTS)
- `doc/requirement/README.md` - Requirement doc format
- `doc/feature/README.md` - Feature specification format
- `/rule` skill - Engineering rules and doc folder map
- `/architecture` skill - Lean codegen, dependency analysis
