# Simple Doctest (sdoctest)

A Python doctest-inspired interactive test framework for Simple, embedding executable examples directly in documentation and docstrings.

**Goals:**
1. **Documentation as tests** - Code examples in docs are automatically verified
2. **REPL-friendly** - Record actual Simple REPL sessions as tests
3. **Zero boilerplate** - No test framework setup, just `>>>` prompts and expected output
4. **BDD integration** - Discovered and run alongside spec tests

---

## 1. Doctest Syntax

### 1.1 Basic Format (Python-style docstrings)

Doctests use triple-quote blocks (`"""..."""`) similar to Python for functions and classes. They can appear:
- **Immediately before** the function/class definition (no empty line between)
- **Immediately after** the function/class header (no empty line)

Doctest examples within `"""` blocks are wrapped with Markdown code fences to clearly separate description from executable examples:

```simple
# Style 1: Block before function
"""
Computes factorial of n

Examples:
```sdoctest
>>> factorial 5
120
>>> factorial 0
1
```
"""
fn factorial(n: Int) -> Int:
    if n <= 1: return 1
    return n * factorial(n - 1)
```

```simple
# Style 2: Block after function header (no empty line)
fn factorial(n: Int) -> Int:
"""
Computes factorial of n

Examples:
```sdoctest
>>> factorial 5
120
>>> factorial 0
1
```
"""
    if n <= 1: return 1
    return n * factorial(n - 1)
```

**Syntax Structure:**
- `"""..."""` - Outer docstring block (contains description + examples)
- ` ```sdoctest ... ``` ` - Markdown code fence marking executable doctest examples (language hint: `sdoctest` or `simple`)
- Lines starting with `>>>` are executed in a REPL-like environment
- Following lines (without `>>>` or `...`) are expected output
- Empty lines separate examples

### 1.2 Multi-line Statements

```simple
"""
Process a list of numbers

Examples:
```sdoctest
>>> nums = [1, 2, 3]
>>> for x in nums:
...     print x * 2
2
4
6
```
"""
fn process_nums():
    pass
```

**Continuation lines:** Use `...` for indented continuation (loops, blocks, etc.)

### 1.3 Expected Exceptions

```simple
"""
Divide two numbers

Examples:
```sdoctest
>>> divide 10, 0
Error: DivisionByZero
>>> parse_int "not a number"
Error: ParseError: invalid digit
```
"""
fn divide(a, b):
    pass
```

**Exception format:** `Error: ExceptionType` or `Error: ExceptionType: message`

### 1.4 Wildcard Matching

```simple
"""
Generate a unique identifier

Examples:
```sdoctest
>>> generate_uuid()
"........-....-....-....-............"
>>> get_timestamp()
1702......
```
"""
fn generate_uuid():
    pass
```

**Wildcards:**
- `.` matches any single character
- `*` matches any sequence (greedy)
- Use for timestamps, UUIDs, memory addresses, non-deterministic output

### 1.5 Setup/Teardown Blocks

```simple
"""
Database operations with cleanup

Setup:
```sdoctest
>>> db = Database.connect("test.db")
>>> db.clear()
```

Examples:
```sdoctest
>>> user = User.new(name: "Alice")
>>> db.save(user)
>>> db.find_by_name("Alice").name
"Alice"
```

Teardown:
```sdoctest
>>> db.close()
```
"""
fn database_example():
    pass
```

**Execution order:** Setup → Example → Teardown (per doctest block)

---

## 2. Discovery and Execution

### 2.1 Discovery Locations

| Location | Priority | Purpose |
|----------|----------|---------|
| Function/method docstrings (`"""..."""`) | High | API examples |
| Module-level docs (`///` comments) | Medium | Package overview |
| Markdown `.md` files | Low | Tutorials, guides |
| Dedicated `.sdt` files | High | Standalone doctest suites |

### 2.2 File Patterns

```
src/**/*.spl         # Extract from """ blocks (with ```sdoctest fences for examples)
doc/**/*.md          # Extract from code blocks marked ```sdoctest or ```simple-doctest
test/doctest/**/*.sdt # Standalone doctest files (raw doctest format)
```

### 2.3 Execution Modes

**Mode 1: Inline (default)**
- Execute in order within docstring
- Each `>>>` line shares state with previous lines
- Isolated per docstring (fresh REPL context)

**Mode 2: Isolated examples**
```simple
/// @doctest(mode: isolated)
/// >>> x = 1  # Each example gets fresh context
/// >>> x      # This would fail in inline mode
/// Error: NameError: x not defined
```

**Mode 3: Interactive capture**
```bash
$ simple repl --record mytest.sdt
>>> stack = Stack.new
>>> stack.push 42
>>> stack.pop
42
>>> ^D
Saved 4 interactions to mytest.sdt
```

---

## 3. Integration with BDD Spec Framework

### 3.1 Runner Integration

Doctests are discovered and listed alongside spec tests:

```bash
$ simple test --list
Unit specs:        127 examples
Integration specs:  43 examples
System specs:       18 examples
Doctests:           89 examples
  From docstrings:  67
  From .md files:   15
  From .sdt files:   7

Total: 277 examples
```

### 3.2 Execution

```bash
# Run all tests (specs + doctests)
$ simple test --all

# Run only doctests
$ simple test --doctest

# Run doctests for specific module
$ simple test --doctest src/lib/std/collections.spl

# Run doctests with specific tag
$ simple test --doctest --tag examples
```

### 3.3 Coverage Integration

Doctests contribute to integration-level coverage:
- Executed lines marked as covered
- Public functions with doctest examples count toward public function touch coverage
- Reported separately in coverage output:

```
Public Function Touch Coverage:
  From integration specs: 87/100 (87%)
  From doctests:         98/100 (98%)
  Combined:              100/100 (100%)
```

### 3.4 BDD-Style Reporting

Doctests appear in test output as examples:

```
Doctest: std.collections.Stack
  >>> Stack.new.push(1).pop                             ✓
  >>> Stack.new.pop raises EmptyStackError              ✓
  
Doctest: std.math.factorial
  >>> factorial 5                                       ✓
  >>> factorial 0                                       ✓
  >>> factorial -1 raises ValueError                    ✓

Finished in 0.43s
5 examples, 0 failures
```

---

## 4. Implementation Architecture

### 4.1 Component Structure

```
lib/std/doctest/
  __init__.spl           # Re-exports
  parser.spl             # Parse >>> examples from strings
  runner.spl             # Execute examples in isolated REPL
  matcher.spl            # Match output (exact, wildcard, exception)
  discovery.spl          # Find doctests in .spl, .md, .sdt files
  reporter.spl           # Format doctest results
  integration.spl        # Hook into std.spec.runner
```

### 4.2 Parser Module

**Responsibilities:**
- Extract doctest blocks from docstrings (`///` comments)
- Parse Markdown code blocks (` ```simple-doctest `)
- Parse `.sdt` files (pure doctest format)
- Identify `>>>`, `...`, expected output, errors

**Output:** `List[DoctestExample]`

```simple
struct DoctestExample:
    source: String           # Original docstring/file
    location: SourceLocation # File:line
    setup: List[String]      # >>> lines from Setup block
    code: List[String]       # >>> and ... lines
    expected: Expected       # Output or exception
    teardown: List[String]   # >>> lines from Teardown
    tags: Set[String]        # @doctest(tag: ...) metadata
```

### 4.3 Runner Module

**Responsibilities:**
- Create isolated REPL environment per docstring
- Execute setup → code → teardown
- Capture stdout/stderr
- Catch exceptions

**Execution flow:**
```
1. Fresh REPL context
2. Execute setup lines (suppress output)
3. Execute code lines
4. Capture output
5. Execute teardown (suppress output)
6. Match output vs expected
7. Report pass/fail
```

### 4.4 Matcher Module

**Match strategies:**
- Exact string match (default)
- Wildcard match (`.` and `*`)
- Exception match (`Error: Type` or `Error: Type: message`)
- Normalized match (strip trailing whitespace, normalize newlines)

### 4.5 Discovery Module

**Discovery algorithm:**
1. Walk source tree for `.spl` files
2. Extract `"""..."""` blocks (docstring blocks for functions/classes/modules)
3. Within each `"""` block, extract ` ```sdoctest ... ``` ` fenced sections (contains actual doctest examples)
4. Match blocks to preceding/following functions/classes (no empty line rule)
5. Parse ` ```sdoctest ` sections for `>>>` examples, `...` continuations, expected output
6. Extract `///` module-level docs for module/package examples
7. Walk doc tree for `.md` files with ` ```sdoctest ` or ` ```simple-doctest `
8. Walk `test/doctest/` for `.sdt` files
9. Build `List[DoctestExample]`

**Filtering:**
- `--tag` filters examples by metadata
- `--file` filters by source location
- `--skip-slow` skips examples tagged `@doctest(tag: slow)`

**Matching rules:**
- `"""` block immediately before function/class = belongs to that function/class
- `"""` block immediately after function/class header = belongs to that function/class
- No empty line between `"""` and target = automatic association

### 4.6 Integration with spec.runner

**Hook points:**
1. **Discovery phase:** `spec.runner` calls `doctest.discovery.find_all()`
2. **Registration:** Doctests registered as synthetic spec examples
3. **Execution:** Runner dispatches to `doctest.runner.run(example)`
4. **Reporting:** Failures reported via same formatter as specs

**Synthetic spec example:**
```simple
# Internally, doctest integration creates:
describe "Doctest: std.math":
    it ">>> factorial 5":
        result = doctest.runner.run(example)
        expect result to eq Pass
```

---

## 5. CLI and Configuration

### 5.1 CLI Commands

```bash
# Discover and list doctests
simple doctest --list

# Run all doctests
simple doctest

# Run doctests for specific file
simple doctest src/lib/std/collections.spl

# Run with filter
simple doctest --match "factorial"

# Record interactive session
simple repl --record output.sdt

# Verify doctests in CI
simple doctest --fail-fast --quiet
```

### 5.2 Configuration (simple.toml)

```toml
[test.doctest]
enabled = true
discovery = ["src/lib/**/*.spl", "doc/**/*.md"]
exclude = ["src/internal/**"]
mode = "inline"  # or "isolated"
timeout_ms = 5000
fail_fast = false

[test.doctest.tags]
default_tags = ["examples"]
skip_tags = ["slow", "manual"]
```

### 5.3 Metadata Attributes

```simple
/// @doctest(mode: isolated, tag: slow, timeout: 10000)
/// >>> expensive_computation()
/// 42
```

**Supported attributes:**
- `mode: inline | isolated` - Execution mode
- `tag: String | List[String]` - Tags for filtering
- `timeout: Int` - Max execution time (ms)
- `skip: Bool` - Skip this doctest
- `skip_reason: String` - Why skipped

---

## 6. Examples by Use Case

### 6.1 API Documentation

```simple
"""
Creates a new stack with initial capacity

```sdoctest
>>> s = Stack.new(capacity: 10)
>>> s.capacity
10
>>> s.size
0
```
"""
struct Stack:
    capacity: Int
    items: List[T]
```

### 6.2 Tutorial (Markdown)

````markdown
# Simple Collections Tutorial

## Stacks

Simple provides a `Stack` data structure:

```simple-doctest
>>> stack = Stack.new
>>> stack.push(1)
>>> stack.push(2)
>>> stack.pop
2
>>> stack.pop
1
```
````

### 6.3 Error Handling

```simple
"""
Parses integer from string

```sdoctest
>>> parse_int "123"
123
>>> parse_int "12.3"
Error: ParseError: invalid character '.'
>>> parse_int ""
Error: ParseError: empty string
```
"""
fn parse_int(s: String) -> Int:
    ...
```

### 6.4 Stateful Examples

```simple
"""
Database connection

Setup:
```sdoctest
>>> db = Database.connect(":memory:")
```

Examples:
```sdoctest
>>> db.execute("CREATE TABLE users (id INT, name TEXT)")
>>> db.execute("INSERT INTO users VALUES (1, 'Alice')")
>>> db.query("SELECT name FROM users").first
"Alice"
```

Teardown:
```sdoctest
>>> db.close()
```
"""
fn database_example():
    ...
```

### 6.5 Standalone Test Suite (.sdt)

```simple
# test/doctest/collections/stack_examples.sdt

# Basic operations
>>> stack = Stack.new
>>> stack.push(42)
>>> stack.peek
42
>>> stack.pop
42

# Empty stack error
>>> Stack.new.pop
Error: EmptyStackError

# Multiple pushes
>>> s = Stack.new
>>> for i in [1, 2, 3]:
...     s.push(i)
>>> s.size
3
```

---

## 7. Implementation Plan

### Phase 1: Core Parser and Runner (Sprint 1)
**Goal:** Parse and execute basic doctests

1. ✅ Create `lib/std/doctest/` structure
2. ⏳ Implement `parser.spl`:
   - Extract `>>>` examples from strings
   - Parse expected output
   - Parse exception expectations
3. ⏳ Implement `runner.spl`:
   - Execute code in isolated REPL
   - Capture output
   - Match against expected
4. ⏳ Write unit tests for parser and runner
5. ⏳ Manual testing with sample docstrings

**Deliverable:** Can parse and run inline doctests from strings

### Phase 2: Discovery and Integration (Sprint 2)
**Goal:** Auto-discover doctests and integrate with spec framework

1. ✅ Enhanced `discovery.spl`:
   - File walking framework
   - Markdown doctest extraction
   - Glob pattern include/exclude (stub)
2. ✅ Created integration test spec
3. ✅ Created test fixtures (sample.spl, sample.sdt, tutorial.md)
4. ⏳ Implement file system helpers:
   - `walk_directory()` - recursive file tree traversal
   - `path_exists()` - check path existence
   - `read_file()` - read file contents
5. ⏳ Implement `integration.spl`:
   - Hook into `spec.runner` discovery
   - Create synthetic spec examples
   - Report via spec formatters
6. ⏳ Write integration tests
7. ⏳ Update `simple test` CLI to include doctests

**Deliverable:** `simple test --doctest` works end-to-end

### Phase 3: Advanced Features (Sprint 3)
**Goal:** Wildcards, setup/teardown, tags

1. ⏳ Implement wildcard matching (`.` and `*`)
2. ⏳ Implement setup/teardown blocks
3. ⏳ Implement tag filtering
4. ⏳ Implement `--record` mode for REPL
5. ⏳ Write system tests for advanced features

**Deliverable:** Full feature parity with Python doctest

### Phase 4: Coverage and Polish (Sprint 4)
**Goal:** Coverage integration and production-ready

1. ⏳ Integrate with coverage reporting
2. ⏳ Add `simple.toml` configuration support
3. ⏳ Write comprehensive examples
4. ⏳ Update `doc/spec/bdd_spec.md` with doctest section
5. ⏳ Migration guide for existing code

**Deliverable:** Production-ready, documented, tested

---

## 8. Success Criteria

**Phase 1 (Core):**
- [ ] Parse `>>>` examples from strings
- [ ] Execute examples and capture output
- [ ] Match exact output
- [ ] Match exception types
- [ ] 20+ unit tests passing

**Phase 2 (Integration):**
- [ ] Discover doctests from `.spl` docstrings
- [ ] Discover doctests from `.md` files
- [ ] Discover doctests from `.sdt` files
- [ ] Run via `simple test --doctest`
- [ ] Report pass/fail in test output
- [ ] 10+ integration tests passing

**Phase 3 (Advanced):**
- [ ] Wildcard matching works
- [ ] Setup/teardown isolation works
- [ ] Tag filtering works
- [ ] REPL recording works
- [ ] 15+ system tests passing

**Phase 4 (Polish):**
- [ ] Coverage integration complete
- [ ] Documentation complete
- [ ] Example library (10+ real-world doctests)
- [ ] Zero regressions in existing tests

**Overall:**
- [ ] 100% of public API has doctest examples
- [ ] Doctests contribute to public function touch coverage
- [ ] CI runs doctests on every commit
- [ ] Developer documentation includes doctest guide

---

## 9. Comparison with Python doctest

| Feature | Python doctest | Simple doctest |
|---------|----------------|----------------|
| Docstring syntax | `"""..."""` | `"""..."""` (Python-style) |
| Prompt | `>>>` and `...` | `>>>` and `...` |
| Discovery | Module docstrings | Function/class `"""` blocks, module `///` docs, `.md` + `.sdt` |
| Block placement | Anywhere in docstring | Before/after function/class (no empty line rule) |
| Execution | Module globals | Isolated REPL |
| Wildcards | `...` (ellipsis) | `.` and `*` |
| Setup/Teardown | Manual | Built-in blocks |
| BDD Integration | None | Native via spec.runner |
| Coverage | None | Integrated |
| REPL Recording | None | `--record` flag |
| Tags/Metadata | None | `@doctest(...)` |

**Key improvements:**
- Simple doctest uses Python's triple-quote syntax for familiarity
- Automatic association of `"""` blocks with functions/classes
- Clean separation: `"""` for functions, `///` for modules/legacy
- First-class citizen of the test framework, not an afterthought

---

## 10. Related Documents

- `doc/spec/bdd_spec.md` - BDD spec framework (parent framework)
- `doc/test.md` - Test policy and coverage rules
- `doc/spec/language.md` - Simple language spec (REPL semantics)

---

## 11. Open Questions

1. **REPL implementation:** Does Simple have a working REPL interpreter? If not, doctests can use the regular interpreter with captured I/O.
2. **Docstring extraction:** Does the parser expose docstrings in the AST? If not, we can regex-parse `///` comments.
3. **Markdown parsing:** Should we vendor a markdown parser or require a specific format (e.g., fence with `simple-doctest` tag)?
4. **Performance:** Should doctests run in parallel or serial? (Serial is safer for REPL state isolation.)

---

**Status:** Specification complete, ready for implementation.

**Next steps:**
1. Update `TODO.md` with phased plan
2. Create `lib/std/doctest/` skeleton
3. Implement Phase 1 (parser + runner) in TDD style
4. Write first integration test (parse → run → pass/fail)
