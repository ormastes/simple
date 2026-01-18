# System Test Framework

**Status:** Active
**Last Updated:** 2025-12-18

This document describes how to write system-level tests for the Simple language compiler and runtime using the BDD spec framework and SDN configuration format.

---

## Overview

System tests validate end-to-end behavior with minimal mocking:
- **CLI tests** - Compiler, interpreter, watcher command-line interfaces
- **Feature tests** - Language features working together
- **Integration tests** - Cross-module behavior

### Test Organization

```
simple/test/system/
├── compiler/          # Compiler CLI tests (1 file)
│   └── compiler_sample_spec.spl
├── interpreter/       # Interpreter CLI tests (1 file)
│   └── interpreter_sample_spec.spl
├── watcher/           # File watcher tests (1 file)
│   └── watcher_app_spec.spl
└── features/          # Language feature tests (62+ files)
    ├── actors/
    ├── array_types/
    ├── async_effects/
    └── ...
```

### Auto-Discovery

System tests are automatically discovered and integrated with Rust's test framework:

```bash
# Run all system tests (65 tests)
cargo test -p simple-driver --test simple_tests

# Run specific subsystem
cargo test -p simple-driver simple_test_system_compiler
cargo test -p simple-driver simple_test_system_features
```

---

## Data Formats

### SDN - Simple Data Notation

System test configuration uses SDN for embedded data. See **[SDN Specification](../spec/sdn.md)** for full grammar.

**Quick Reference - Table Types:**

| Kind | Syntax | Colon | Delimiter |
|------|--------|-------|-----------|
| Typed table | `name: table{i32, i32}` | ✅ | Comma |
| Named table | `name \|f1, f2\|` | ❌ | Comma |

**Example:**
```sdn
test_cases |name, timeout, tags|
    "array indexing", 1000, [core]
    "async spawn", 5000, [async]
```

### Gherkin DSL - Examples Tables

For parameterized system tests, use `examples` tables with two-space delimiter. See **[Gherkin DSL Specification](../spec/testing/testing_bdd_framework.md)** for full grammar.

**Quick Reference:**

| Kind | Syntax | Colon | Delimiter |
|------|--------|-------|-----------|
| Examples table | `examples name:` | ✅ | Two-space |

**Example:**
```simple
examples addition:
    a    b    result
    1    2    3
    10   20   30
```

---

## BDD Spec Framework

System tests use the BDD spec framework with Given-When-Then pattern.

### Basic Structure

```simple
use spec.*

describe "Feature Name":
    context "when condition":
        it "does something":
            # Arrange (Given)
            setup = create_test_environment()

            # Act (When)
            result = perform_action(setup)

            # Assert (Then)
            expect(result).to_equal(expected)
```

### Given-When-Then Pattern

**Using Context Definitions:**

```simple
context_def :empty_stack:
    # Given: initial state
    given_lazy :stack, \:
        Stack.new()

describe "Stack":
    context :empty_stack:
        context "when pushed":
            # When: action
            given:
                stack.push(42)

            # Then: verify
            it "size increases":
                expect stack.size() == 1

            it "top is correct":
                expect stack.top() == 42
```

### System Test Example

```simple
use spec.*
use std.process.*
use std.fs.*

describe "Simple Compiler CLI":
    context "when compiling valid source":
        given_lazy :source_file, \:
            temp_file("test.spl", "main = 42")

        given_lazy :compiled_output, \:
            run_compiler(source_file, "--output", "test.smf")

        it "creates SMF file":
            expect File.exists("test.smf")

        it "exits with code 0":
            expect compiled_output.exit_code == 0

        it "produces valid bytecode":
            smf = File.read_bytes("test.smf")
            expect smf[0..4] == b"SMF\x00"

    context "when compiling invalid syntax":
        given_lazy :source_file, \:
            temp_file("bad.spl", "main = ")

        given_lazy :result, \:
            run_compiler(source_file)

        it "fails with non-zero exit code":
            expect result.exit_code != 0

        it "shows syntax error":
            expect result.stderr.contains("SyntaxError")
```

---

## Test Discovery

### File Patterns

Tests are auto-discovered using these patterns:
- `*_spec.spl` - BDD-style specification tests (preferred)
- `*_test.spl` - Traditional test files
- `fixtures/` directories are skipped

### Running Tests

```bash
# Run all Simple language tests (96 total: 31 stdlib + 65 system)
cargo test -p simple-driver

# Run only stdlib tests (31 tests)
cargo test -p simple-driver --test simple_stdlib_tests

# Run only system tests (65 tests)
cargo test -p simple-driver --test simple_tests

# Run specific test category
cargo test -p simple-driver simple_test_system_compiler
cargo test -p simple-driver simple_test_system_interpreter
cargo test -p simple-driver simple_test_system_features

# Run specific feature test
cargo test -p simple-driver simple_test_system_features_actors_actors_spec
```

### Test Organization

| Directory | Count | Purpose |
|-----------|-------|---------|
| `simple/std_lib/test/` | 31 | Standard library tests |
| `simple/test/system/` | 65 | System-level CLI and feature tests |
| **Total** | **96** | **All auto-integrated with cargo test** |

---

## Writing System Tests

### CLI Testing Pattern

```simple
use spec.*
use std.process.*
use std.io.*

describe "CLI Tool":
    fn run_cli(*args):
        Process.run("simple", args)

    context "with valid input":
        it "succeeds":
            result = run_cli("run", "examples/hello.spl")
            expect result.is_success()
            expect result.stdout == "Hello, World!\n"

    context "with invalid flags":
        it "shows help message":
            result = run_cli("--invalid-flag")
            expect result.exit_code != 0
            expect result.stderr.contains("Usage:")
```

### File Watcher Testing

```simple
use spec.*
use std.process.*
use std.fs.*
use std.time.*

describe "File Watcher":
    context "when source file changes":
        it "rebuilds automatically":
            # Start watcher in background
            watcher = Process.spawn("simple", ["watch", "src/main.spl"])

            # Wait for initial build
            sleep(1000)

            # Modify source
            File.write("src/main.spl", "main = 100")

            # Wait for rebuild
            sleep(1000)

            # Check output contains rebuild message
            output = watcher.read_stdout()
            expect output.contains("Rebuilding")

            # Cleanup
            watcher.kill()
```

---

## Integration with Rust Tests

System tests are wrapped as Rust tests via `build.rs`:

```rust
// Auto-generated by build.rs
#[test]
fn simple_test_system_compiler_compiler_sample_spec() {
    let result = std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024) // 8MB stack
        .spawn(|| {
            let path = Path::new("simple/test/system/compiler/compiler_sample_spec.spl");
            run_test_file(path)
        })
        .expect("Failed to spawn test thread")
        .join()
        .expect("Test thread panicked");

    match result {
        SimpleTestResult::Pass { .. } => (),
        SimpleTestResult::Fail { failures, .. } => panic!("Test failed: {:?}", failures),
        SimpleTestResult::CompileError { error, .. } => panic!("Compile error: {}", error),
        SimpleTestResult::RuntimeError { error, .. } => panic!("Runtime error: {}", error),
    }
}
```

---

## Living Documentation Generation

### Overview

System tests written in BDD spec format can automatically generate human-readable documentation, similar to Cucumber's living documentation feature. This creates up-to-date manuals directly from executable specifications.

### Concept

```
BDD Spec Tests (*.spl)
        ↓
    Test Runner
        ↓
Living Documentation Generator
        ↓
   HTML / Markdown
```

### Output Formats

**HTML Documentation:**
- Interactive navigation (collapsible sections)
- Test status indicators (✅ passing, ❌ failing, ⏭️ skipped)
- Syntax highlighting for code examples
- Search and filter capabilities

**Markdown Documentation:**
- Flat file format for static sites
- GitHub-compatible rendering
- Version control friendly
- Easy to diff and review

### Generated Structure

From this spec:

```simple
describe "User Authentication":
    context "when user has valid credentials":
        it "grants access":
            user = create_user(email: "test@example.com", password: "secret123")
            result = authenticate(user.email, "secret123")
            expect result.is_success()

    context "when user has invalid credentials":
        it "denies access":
            user = create_user(email: "test@example.com", password: "secret123")
            result = authenticate(user.email, "wrong_password")
            expect result.is_failure()
```

Generates this documentation:

```markdown
# User Authentication

## When user has valid credentials

✅ **grants access**

Creates a user with valid credentials and verifies that authentication succeeds.

## When user has invalid credentials

✅ **denies access**

Creates a user and verifies that authentication fails with incorrect password.
```

### CLI Usage

```bash
# Generate HTML documentation
simple test --format html --output doc/specs/

# Generate Markdown documentation
simple test --format markdown --output doc/specs.md

# Generate with test results
simple test --doc --html-output docs/test-report.html

# Watch mode - regenerate on file changes
simple test --doc --watch --output docs/
```

### Configuration

**simple.toml:**

```toml
[test.documentation]
# Output format: html, markdown, json
format = "html"

# Output directory
output = "doc/specs"

# Include test status in documentation
include_status = true

# Include code examples
include_examples = true

# Template customization
template = "docs/template.html"

# Sections to include
sections = ["description", "examples", "given-when-then"]
```

### Template Variables

Custom HTML templates can use these variables:

```html
<!DOCTYPE html>
<html>
<head>
    <title>{{suite_name}} - Test Specifications</title>
</head>
<body>
    {{#each describe_blocks}}
    <section class="describe">
        <h2>{{description}}</h2>
        {{#each contexts}}
        <div class="context">
            <h3>{{description}}</h3>
            {{#each examples}}
            <div class="example {{status}}">
                <h4>{{description}}</h4>
                <pre><code>{{code}}</code></pre>
                {{#if failure}}
                <div class="failure">{{failure.message}}</div>
                {{/if}}
            </div>
            {{/each}}
        </div>
        {{/each}}
    </section>
    {{/each}}
</body>
</html>
```

### Status: ✅ 100% COMPLETE (8/8 components)

| Component | Status | Description |
|-----------|--------|-------------|
| HTML Generator | ✅ | Convert spec AST to HTML with templates (simple/std_lib/src/spec/formatter/html.spl) |
| Markdown Generator | ✅ | Convert spec AST to Markdown (simple/std_lib/src/spec/formatter/markdown.spl) |
| Template Engine | ✅ | Built-in HTML template with CSS (default_template() function) |
| Test Status Integration | ✅ | Pass/fail/skip indicators (✅❌⏭️) in both formats |
| Code Example Extraction | ✅ | Syntax-highlighted code blocks in HTML and Markdown |
| CLI Integration | ✅ | `simple test --doc` command generates docs/ directory |
| Watch Mode | ✅ | Auto-regenerate on file changes with `simple test --watch --doc` |
| Custom Templates | ✅ | Support via HtmlFormatter.new_with_template() |

**Implementation Files:**
- **Stdlib Formatters:**
  - `simple/std_lib/src/spec/formatter/__init__.spl` - Module exports
  - `simple/std_lib/src/spec/formatter/html.spl` - HTML generator (240 lines)
  - `simple/std_lib/src/spec/formatter/markdown.spl` - Markdown generator (95 lines)
  - Exported from `simple/std_lib/src/spec/__init__.spl`
- **Driver Integration:**
  - `src/driver/src/cli/test_runner.rs` - CLI integration (372 lines added)
  - Functions: generate_documentation(), generate_html_doc(), generate_markdown_doc(), html_escape(), watch_tests()
  - Watch mode: Filesystem monitoring with notify crate, auto-detect changes, re-run tests

**Usage:**
```bash
# Run tests and generate documentation (one-time)
simple test --doc

# Watch mode: auto-rerun and regenerate on changes
simple test --watch --doc

# Watch specific test levels
simple test --watch --unit
simple test --watch --system

# Output files:
docs/test-spec.html   # Interactive HTML with CSS
docs/test-spec.md     # GitHub-compatible Markdown
```

**Tracking:** Feature request #650 - Living Documentation Generation ✅ 100% COMPLETE

---

## Gherkin-Style System Tests

For complex system tests with parameterized data, use the Gherkin-style DSL with `feature`, `scenario`, and `examples` keywords.

See **[Gherkin DSL Specification](../spec/testing/testing_bdd_framework.md)** for full grammar.

### Quick Example

```simple
examples addition:
    a    b    result
    1    2    3
    10   20   30

context calculator at <n>:
    calc = Calculator.new().set(n)

feature Arithmetic:
    scenario outline Adding numbers:
        given calculator at 0:
        when add <a>:
        when add <b>:
        then value is <result>:

        examples addition:
```

---

## See Also

- [BDD Spec Framework](../spec/testing/testing_bdd_framework.md) - `describe`/`context`/`it` DSL
- [Gherkin DSL](../spec/testing/testing_bdd_framework.md) - `feature`/`scenario`/`examples` DSL
- [SDN Format](../spec/sdn.md) - Data notation for configuration
- [Test Policy](test.md) - Coverage metrics and test levels
- `simple/std_lib/test/` - Standard library test examples
