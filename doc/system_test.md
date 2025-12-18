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

## SDN - Simple Data Notation

System test configuration uses SDN (Simple Data Notation), a minimal, token-efficient format for embedded data.

### Design Goals

1. **Minimal syntax** - No unnecessary punctuation
2. **One-pass parsing** - LL(2) max lookahead
3. **Token efficient** - Optimized for LLM context windows
4. **Human readable** - Clear visual structure
5. **Embeddable** - Works as standalone `.sdn` files or embedded in Simple code

### Grammar (EBNF)

```ebnf
(* === TOP LEVEL === *)
document     = statement* ;

statement    = ident ':' value NEWLINE                          (* simple value *)
             | ident '=' inline_value NEWLINE                   (* short dict/array *)
             | ident ':' NEWLINE INDENT block DEDENT            (* long dict/array *)
             | ident ':' table_type '=' '[' tuple_list ']' NEWLINE    (* short typed table *)
             | ident ':' table_type NEWLINE INDENT rows DEDENT  (* long typed table *)
             | ident '|' field_list '|' row                     (* short named table *)
             | ident '|' field_list '|' NEWLINE INDENT rows DEDENT    (* long named table *)
             | COMMENT NEWLINE
             | NEWLINE
             ;

(* === VALUES === *)
value        = bare_string
             | quoted_string
             | number
             | bool
             | null
             | inline_value
             ;

inline_value = '{' pair_list? '}'                               (* dict *)
             | '[' value_list? ']'                              (* array *)
             ;

pair_list    = pair (',' pair)* ','? ;
pair         = ident ':' value ;

value_list   = value (',' value)* ','? ;

(* === BLOCKS === *)
block        = dict_block
             | array_block
             ;

dict_block   = (ident ':' value NEWLINE)+ ;

array_block  = (value NEWLINE)+ ;

(* === TABLES === *)
table_type   = 'table' '{' type_list '}' ;
type_list    = type_name (',' type_name)* ;
type_name    = ident ;

field_list   = ident (',' ident)* ;

tuple_list   = tuple (',' tuple)* ;
tuple        = '(' value_list ')' ;

rows         = row+ ;
row          = value (',' value)* NEWLINE ;

(* === TOKENS === *)
ident        = [A-Za-z_][A-Za-z0-9_]* ;
bare_string  = [A-Za-z_][A-Za-z0-9_./:-]* ;      (* extended chars for paths/urls *)
quoted_string = '"' ([^"\\] | '\\' .)* '"' ;
number       = '-'? [0-9]+ ('.' [0-9]+)? ([eE] [+-]? [0-9]+)? ;
bool         = 'true' | 'false' ;
null         = 'null' | 'nil' ;
COMMENT      = '#' [^\n]* ;
NEWLINE      = '\n' | '\r\n' ;
INDENT       = <increase in indentation> ;
DEDENT       = <decrease in indentation> ;
```

### Syntax Examples

#### Assignment Operators

| Operator | Usage | Form |
|----------|-------|------|
| `:` | Simple value or block start | Long form |
| `=` | Inline dict/array | Short form |
| `\|...\|` | Named table fields | Table form |

#### Primitives

```sdn
# Simple values (colon)
name: Alice
age: 30
active: true
ratio: 3.14

# Quote-free strings (identifier-like)
city: Boulder
status: pending

# Quoted strings (spaces/special chars)
message: "Hello, World!"
path: "/home/user/data"
```

#### Dict (Object)

**Short Form (inline with `=`):**

```sdn
point = {x: 10, y: 20}
config = {host: localhost, port: 8080, debug: true}
nested = {outer: {inner: value}}
```

**Long Form (block with `:`):**

```sdn
server:
    host: localhost
    port: 8080
    debug: true

# Nested blocks
database:
    primary:
        host: db1.example.com
        port: 5432
    replica:
        host: db2.example.com
        port: 5432
```

#### Array

**Short Form:**

```sdn
numbers = [1, 2, 3, 4, 5]
names = [Alice, Bob, Carol]
mixed = [1, "two", true, null]
```

**Long Form:**

```sdn
items:
    apple
    banana
    cherry

config_list:
    {name: dev, port: 3000}
    {name: prod, port: 8080}
```

#### Tables

**Named Fields (flexible types):**

```sdn
# Short form
users |id, name, active| 1, Alice, true

# Long form
employees |id, name, title, salary, remote|
    1001, Alice Chen, "Senior Engineer", 150000, true
    1002, Bob Smith, "Staff Engineer", 180000, false
    1003, Carol Jones, "Engineering Manager", 200000, true
```

**Typed Columns (strict types):**

```sdn
# Short form
points: table{i32, i32} = [(10, 20), (30, 40)]

# Long form
coordinates: table{f64, f64, f64}
    1.0, 2.0, 3.0
    4.0, 5.0, 6.0
    7.0, 8.0, 9.0
```

### Complete Example: Test Configuration

```sdn
# System test configuration

test_suite: language_features
environment: system
timeout: 30_000

compiler:
    backend: llvm
    optimization: O2
    debug_info: true

runtime:
    gc_enabled: true
    stack_size: 8388608      # 8MB
    heap_size: 536870912     # 512MB

test_cases |name, timeout, tags, skip|
    "array indexing", 1000, [core, arrays], false
    "async spawn", 5000, [async, concurrency], false
    "gpu kernels", 10000, [gpu, simd], false

expected_failures = [
    "known_bug_123",
    "platform_specific_feature"
]

matrix:
    platforms = [linux, macos, windows]
    variants = [debug, release]
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
            expect File.exists?("test.smf")

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
            expect result.success?
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
            expect result.success?

    context "when user has invalid credentials":
        it "denies access":
            user = create_user(email: "test@example.com", password: "secret123")
            result = authenticate(user.email, "wrong_password")
            expect result.failure?
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
simple test --format html --output docs/specs/

# Generate Markdown documentation
simple test --format markdown --output docs/specs.md

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
output = "docs/specs"

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

### Status: ✅ COMPLETE (7/8 components, 87.5%)

| Component | Status | Description |
|-----------|--------|-------------|
| HTML Generator | ✅ | Convert spec AST to HTML with templates (simple/std_lib/src/spec/formatter/html.spl) |
| Markdown Generator | ✅ | Convert spec AST to Markdown (simple/std_lib/src/spec/formatter/markdown.spl) |
| Template Engine | ✅ | Built-in HTML template with CSS (default_template() function) |
| Test Status Integration | ✅ | Pass/fail/skip indicators (✅❌⏭️) in both formats |
| Code Example Extraction | ✅ | Syntax-highlighted code blocks in HTML and Markdown |
| CLI Integration | ✅ | `simple test --doc` command generates docs/ directory |
| Watch Mode | 📋 | Auto-regenerate on file changes (requires file watcher) |
| Custom Templates | ✅ | Support via HtmlFormatter.new_with_template() |

**Implementation Files:**
- **Stdlib Formatters:**
  - `simple/std_lib/src/spec/formatter/__init__.spl` - Module exports
  - `simple/std_lib/src/spec/formatter/html.spl` - HTML generator (240 lines)
  - `simple/std_lib/src/spec/formatter/markdown.spl` - Markdown generator (95 lines)
  - Exported from `simple/std_lib/src/spec/__init__.spl`
- **Driver Integration:**
  - `src/driver/src/cli/test_runner.rs` - CLI integration (260 lines added)
  - Functions: generate_documentation(), generate_html_doc(), generate_markdown_doc(), html_escape()

**Usage:**
```bash
# Run tests and generate documentation
simple test --doc

# Output files:
docs/test-spec.html   # Interactive HTML with CSS
docs/test-spec.md     # GitHub-compatible Markdown
```

**Tracking:** Feature request #650 - Living Documentation Generation ✅ 87.5% COMPLETE (7/8)

---

## See Also

- `doc/spec/bdd_spec.md` - Complete BDD framework specification
- `doc/spec/sdn.md` - Full SDN format specification
- `doc/test.md` - Overall test policy and coverage metrics
- `simple/std_lib/test/` - Standard library test examples
