# Simple Doctest - BDD Spec Integration Plan

This document describes how sdoctest integrates with the existing BDD spec framework.

## Architecture Overview

```
Test Framework Stack:

┌─────────────────────────────────────────────────┐
│         simple test CLI                         │
│  (discovers and runs all test types)            │
└─────────────────────────────────────────────────┘
                     │
        ┌────────────┴────────────┐
        │                         │
┌───────▼────────┐      ┌────────▼─────────┐
│  BDD Spec      │      │    Doctest       │
│  Framework     │◄─────┤    Framework     │
│                │      │                  │
│ (std.spec)     │      │ (std.doctest)    │
└────────────────┘      └──────────────────┘
        │                         │
        │                         │
┌───────▼─────────────────────────▼────────┐
│          Unified Test Runner             │
│  - Discovery                             │
│  - Execution                             │
│  - Reporting (progress, doc, json)       │
│  - Coverage tracking                     │
└──────────────────────────────────────────┘
```

## Component Responsibilities

### std.spec (BDD Framework)
**Owns:**
- Test registry (describe/context/it)
- Hook execution (before_each, after_each, etc.)
- Expectation DSL (expect X to eq Y)
- Matchers (eq, be, include, etc.)
- Runner orchestration
- Formatters (progress, doc, json)
- Coverage tracking and reporting

**Provides to doctest:**
- `Runner` interface for registering examples
- `ExampleGroup` and `Example` abstractions
- Unified reporting via formatters
- Coverage infrastructure

### std.doctest (Doctest Framework)
**Owns:**
- Docstring parsing (`>>>` syntax)
- Wildcard output matching (`.` and `*`)
- Exception matching (`Error: Type`)
- Setup/teardown blocks
- Interpreter integration
- File discovery (.spl, .md, .sdt)

**Integrates with spec via:**
- `integration.spl` - Converts doctests → spec examples
- Registers with spec runner during discovery phase
- Reports via spec formatters (no custom output)

## Integration Points

### 1. Discovery Phase

```simple
# In spec runner initialization:
fn discover_tests() -> TestSuite:
    suite = TestSuite.new()
    
    # 1. Discover BDD specs
    spec_groups = discover_spec_files("test/**/*_spec.spl")
    for group in spec_groups:
        suite.register(group)
    
    # 2. Discover doctests
    doctest_examples = std.doctest.discovery.discover_all(
        config: DiscoveryConfig(
            search_paths: ["lib/", "src/", "doc/"],
            include_patterns: ["**/*.spl", "**/*.md", "**/*.sdt"],
            exclude_patterns: ["**/target/**"]
        )
    )
    
    # 3. Convert doctests to spec examples
    doctest_groups = std.doctest.integration.create_example_groups(doctest_examples)
    for group in doctest_groups:
        suite.register(group)
    
    return suite
```

**Key insight:** Doctests become first-class spec examples, not a separate test type.

### 2. Execution Phase

```simple
# Doctest example converted to spec example:
describe "Doctest: std.collections.Stack":
    it ">>> Stack.new.push(1).pop":
        # This closure wraps the doctest runner
        doctest_runner = DoctestRunner.new()
        result = doctest_runner.run_example(doctest_ex)
        
        # Convert to spec assertion
        match result.result:
            case MatchResult.Pass:
                pass  # Test passes
            case MatchResult.Fail(msg):
                raise AssertionError(msg)  # Test fails via spec mechanism
```

**Key insight:** Doctest failures are surfaced as standard assertion errors.

### 3. Reporting Phase

```
# Progress formatter output:
Unit specs:        127 examples
Integration specs:  43 examples
System specs:       18 examples
Doctests:           89 examples
  From docstrings:  67
  From .md files:   15
  From .sdt files:   7

Running specs:

.................................................F..........

Failures:

1) Doctest: std.math >>> factorial -1 raises ValueError
   Expected exception ValueError, got output: -1

Finished in 1.23s
277 examples, 1 failure
```

**Key insight:** Doctests appear in unified output, not separate section.

### 4. Coverage Integration

```yaml
# Coverage report:
Public Function Touch Coverage:
  From integration specs:  87/100 (87%)
  From doctests:          98/100 (98%)
  Combined:              100/100 (100%)

Missing functions:
  - std.io.read_binary (integration specs)
  - std.math.gcd (integration specs)

Covered by doctests only:
  - std.collections.Stack.push (doctest: lib/std/collections.spl:42)
  - std.text.format (doctest: lib/std/text.spl:18)
```

**Key insight:** Doctests contribute to integration-level coverage metrics.

## File Organization

```
lib/std/
  spec/                   # BDD framework (parent)
    dsl.spl
    registry.spl
    runtime.spl
    expect.spl
    matchers/
    runner/
      cli.spl
      executor.spl
    formatter/
      progress.spl
      doc.spl
      json.spl
    coverage/
      tracker.spl
      reporter.spl
  
  doctest/                # Doctest framework (child)
    __init__.spl
    parser.spl            # Parse >>> examples
    matcher.spl           # Wildcard and exception matching
    runner.spl            # Execute in interpreter
    discovery.spl         # Find doctests in files
    reporter.spl          # Format results
    integration.spl       # Hook into spec.runner

test/
  unit/
    spec/                 # BDD framework tests
    doctest/              # Doctest framework tests
      parser_spec.spl
      matcher_spec.spl
      runner_spec.spl
  integration/
    spec/
    doctest/
  system/
    spec/
    doctest/
```

## CLI Commands

### Basic Usage

```bash
# Run all tests (specs + doctests)
simple test

# Run only BDD specs
simple test --spec

# Run only doctests
simple test --doctest

# Run specific layer + doctests
simple test --unit --doctest
simple test --integration --doctest

# List all tests
simple test --list
```

### Filtering

```bash
# Filter by pattern (matches specs and doctests)
simple test --match "Stack"

# Filter by tag
simple test --tag examples

# Skip slow doctests
simple test --skip-tag slow
```

### Output Formats

```bash
# Progress (default)
simple test

# Doc format (nested describe/context)
simple test --format doc

# JSON (for IDE integration)
simple test --format json
```

### Coverage

```bash
# Run with coverage
simple test --coverage

# Coverage for specific layer
simple test --integration --doctest --coverage

# Show missing public functions
simple test --coverage --show-missing
```

## Implementation Status

### Phase 1: Core Parser and Runner (COMPLETE)
- ✅ Parser with `>>>` syntax
- ✅ Matcher with wildcards and exceptions
- ✅ Runner with setup/teardown
- ✅ 40+ unit tests
- ⏳ Interpreter integration (pending REPL API)

### Phase 2: Discovery and Integration (TODO)
- ⏳ File discovery (.spl, .md, .sdt)
- ⏳ AST-based docstring extraction
- ⏳ Markdown code block parsing
- ⏳ Hook into spec.runner
- ⏳ Integration tests

### Phase 3: Advanced Features (TODO)
- ⏳ Tag filtering
- ⏳ REPL recording mode
- ⏳ Configuration (simple.toml)
- ⏳ System tests

### Phase 4: Coverage and Polish (TODO)
- ⏳ Coverage contribution tracking
- ⏳ Documentation
- ⏳ Example library
- ⏳ Migration guide

## Open Questions

1. **Interpreter API:** Does Simple have a REPL/interpreter API we can use?
   - If yes: Use directly
   - If no: Use tree-walking interpreter from compiler

2. **AST Access:** Can we access docstring nodes from parsed AST?
   - If yes: Use AST traversal
   - If no: Use regex-based `///` comment extraction (current approach)

3. **Execution Isolation:** How to isolate doctest examples?
   - Option A: Fresh interpreter context per docstring (current plan)
   - Option B: Fresh interpreter context per example (slower but safer)
   - Option C: Shared context with explicit reset (faster but riskier)

4. **Coverage Attribution:** How to map executed lines back to public functions?
   - Need `symbols.json` emission from compiler
   - Need line-level coverage from interpreter or LLVM

## Success Criteria

**Phase 1 (Parser/Runner):**
- [x] Parse `>>>` examples from strings
- [x] Wildcard matching works
- [x] Exception matching works
- [x] Setup/teardown isolation
- [x] 40+ unit tests passing

**Phase 2 (Integration):**
- [ ] Discover doctests from `.spl` files
- [ ] Discover doctests from `.md` files
- [ ] Discover doctests from `.sdt` files
- [ ] Run via `simple test --doctest`
- [ ] Unified reporting with BDD specs
- [ ] 20+ integration tests passing

**Phase 3 (Advanced):**
- [ ] Tag filtering works
- [ ] REPL recording mode
- [ ] Configuration via simple.toml
- [ ] 15+ system tests passing

**Phase 4 (Polish):**
- [ ] Coverage integration complete
- [ ] 100% of lib/std has doctest examples
- [ ] Documentation complete
- [ ] CI integration

## Next Steps

1. **Wire interpreter integration**
   - Investigate Simple interpreter/REPL API
   - Implement `execute_line()` in `runner.spl`
   - Test with real Simple code

2. **Implement discovery**
   - File tree walking
   - AST-based docstring extraction (or regex fallback)
   - Markdown code block parsing

3. **Create integration hook**
   - Register doctests with spec.runner
   - Verify unified output
   - Test coverage attribution

4. **System testing**
   - End-to-end workflow tests
   - Real Simple code examples
   - Performance benchmarks

## References

- `doc/spec/sdoctest.md` - Full specification
- `doc/spec/testing/testing_bdd_framework.md` - BDD framework spec
- `doc/guides/test.md` - Test policy and coverage rules
- `lib/std/doctest/` - Implementation
- `test/unit/doctest/` - Unit tests
