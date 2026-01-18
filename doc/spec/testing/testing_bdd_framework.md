# BDD Testing Framework

**Status:** Stable
**Feature IDs:** #302
**Last Updated:** 2025-12-28
**Keywords:** testing, bdd, rspec, describe, it, expect, gherkin
**Topics:** testing

Comprehensive specification for Simple's Ruby/RSpec-style BDD test framework, including traditional BDD syntax, Gherkin-style features, and complete matcher reference.

## Related Specifications
- [Doctest](sdoctest.md) - Inline documentation testing
- [Mock Framework](mock.md) - Test doubles and mocking
- [SDN](sdn.md) - Table syntax integration

---

## Contents

1. [Quick Start](#quick-start)
2. [Folder Layout](#folder-layout)
3. [BDD DSL Syntax](#bdd-dsl-syntax)
4. [Fixtures & Setup](#fixtures--setup)
5. [Matchers Reference](#matchers-reference)
6. [Gherkin-Style Syntax](#gherkin-style-syntax)
7. [Runner & CLI](#runner--cli)
8. [Coverage Policy](#coverage-policy)
9. [Best Practices](#best-practices)
10. [Examples](#examples)

---

## Quick Start

```simple
import std.spec

describe "Calculator":
    context "addition":
        it "adds two numbers":
            expect 2 + 2 == 4

        it "adds negatives":
            expect 5 + (-3) == 2

    context "subtraction":
        it "subtracts numbers":
            expect 10 - 3 == 7
```

Run tests:
```bash
simple test
```

---

## Folder Layout

### Directory Structure

```
test/
  __init__.spl
  environment/
    __init__.spl
    bootstrap.spl
    fixtures/
    helpers/
  unit/
    __init__.spl
    **/*_spec.spl
  integration/
    __init__.spl
    **/*_spec.spl
  system/
    __init__.spl
    **/*_spec.spl
```

### 1. test/ (root)

Provides the test language environment with default imports (`std.*`, `std.spec.*`) and shared helpers (matchers, timeouts, fakes).

### 2. test/environment/

Owns test runtime orchestration:
- Process-level bootstrap (env vars, temp dirs, ports)
- External dependencies (DB containers, mock servers)
- Global spec runner configuration

### 3. test/unit/

Fast, isolated tests for internal behavior.
- Targets: private functions, pure logic, small modules
- Fakes/mocks encouraged
- Coverage: branch/condition

### 4. test/integration/

Validates public functions and module boundaries.
- Targets: exported functions, module-level APIs
- Uses real dependencies where feasible
- Coverage: 100% public function touch

### 5. test/system/

Validates public types and end-to-end flows.
- Targets: public classes/structs with business logic
- Runs with realistic environment via test/environment
- Coverage: 100% public type touch

This follows the test pyramid pattern: more unit tests, fewer system tests.

### Default Imports

#### test/__init__.spl

All files under `test/` implicitly receive:

```simple
import std.*
import std.spec.*
import test.environment.*  # optional
```

#### Per-layer __init__.spl

Set layer-specific defaults:

```simple
# test/system/__init__.spl
import test.*
tag_default :system
timeout_default 30_000
```

---

## BDD DSL Syntax

### 1. Test Groups

**describe** - Top-level group:
```simple
describe "String":
    it "works":
        expect true
```

**context** - Nested group (alias for describe):
```simple
describe "Array":
    context "when empty":
        it "returns 0 length":
            expect [].len() == 0

    context "when populated":
        it "returns length":
            expect [1, 2, 3].len() == 3
```

### 2. Test Cases

```simple
it "description of behavior":
    expect actual == expected
```

### 3. Hooks

| Hook | Scope | Runs |
|------|-------|------|
| `before_each:` | per example | outer → inner |
| `after_each:` | per example | inner → outer |
| `before_all:` | per group | once, outer → inner |
| `after_all:` | per group | once, inner → outer |

Example:
```simple
context "with hooks":
    before_each:
        setup()

    after_each:
        cleanup()

    before_all:
        expensive_init()

    after_all:
        expensive_cleanup()

    it "example":
        expect true
```

### 4. Expectations

**Value expectations:**

```simple
expect actual to eq expected
expect actual not_to eq expected
```

**Direct comparisons:**
```simple
expect 5 == 5
expect "hello" != "world"
expect 10 > 5
expect true                        # truthiness check
```

**Block expectations:**

```simple
expect_raises SomeError:
    do_something()

expect_raises:
    risky_operation()
```

### 5. Shared Examples

```simple
shared_examples "a stack-like container":
    it "supports push/pop":
        s = make()
        s.push(1)
        expect s.pop() to eq 1

describe "Stack":
    fn make() -> Stack:
        return Stack.new()

    it_behaves_like "a stack-like container"
```

### 6. Context Sharing

Define reusable setup groups once, compose them across tests.

**Define:**

```simple
context_def :as_admin:
    given_lazy :user, \:
        create(:user, :admin)

    given:
        login_as(user)

context_def :with_database:
    given:
        db = Database.connect(:test)
        db.migrate()
```

**Reference:**

```simple
describe "AdminDashboard":
    context :as_admin:
        it "shows admin panel":
            expect page.has_selector(".admin-panel")

    context_compose :as_admin, :with_database:
        it "loads from database":
            expect user.data.is_persisted()
```

**Keywords:**

| Keyword | Purpose |
|---------|---------|
| `context_def :name:` | Define reusable context (global registry) |
| `context :symbol:` | Reference context_def (runs its givens) |
| `context_compose :a, :b:` | Compose multiple contexts sequentially |
| `context "string":` | Anonymous nested group |
| `given_lazy :name, \: ...` | Lazy fixture (memoized per example) |
| `given :name, \: ...` | Named eager fixture (runs before each) |
| `given:` | Unnamed eager setup (like before_each) |

**BDD Given-When-Then Pattern:**

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

---

## Fixtures & Setup

### 1. Unnamed Eager Setup

Runs before each example:
```simple
context "setup":
    given:
        setup_database()
        load_fixtures()

    it "works with setup":
        expect true
```

### 2. Lazy Fixtures

Memoized once per example:
```simple
context "with user":
    given_lazy :user, \:
        { name: "Alice", id: 42 }

    it "accesses user":
        expect user.name == "Alice"

    it "same user in example":
        expect user.id == 42
```

### 3. Named Eager Setup

Documented setup step:
```simple
context "complex setup":
    given :db_connect, \:
        database.connect()

    given :load_schema, \:
        database.migrate()

    it "has both setups":
        expect true
```

### 4. Plain Variables

Using let:
```simple
context "with values":
    let x = 10
    let y = 20

    it "calculates sum":
        expect x + y == 30
```

### Fixture Composition

```simple
context_def :setup_a:
    given_lazy :x, \:
        10

context_def :setup_b:
    given_lazy :y, \:
        x + 5  # depends on x from :setup_a

describe "Test":
    context_compose :setup_a, :setup_b:
        given_lazy :z, \:
            y * 2

        it "composes in order":
            # x=10, y=15, z=30
            expect z == 30
```

### Sequential Given Block

```simple
context_def :user_data:
    given_lazy :user, \:
        { name: "Alice", id: 42 }

describe "Test":
    context "with sequential given":
        given:
            given :user_data
            let user_key = "user_" + user.id.to_string()

        it "has derived variables":
            expect user_key == "user_42"
```

---

## Matchers Reference

### Equality & Identity

#### eq - Equality

```simple
expect value to eq expected
expect 42 to eq 42
expect "hello" to eq "hello"
```

#### be - Identity/Equality

```simple
expect value to be expected
expect 5 to be 5
expect "test" to be "test"
```

#### be_nil - Nil Check

```simple
expect value to be_nil
let x: Any = nil
expect x to be_nil
```

### Comparison

#### gt - Greater Than

```simple
expect value to gt other
expect 10 to gt 5      # pass
expect 5 to gt 10      # fail
```

#### lt - Less Than

```simple
expect value to lt other
expect 5 to lt 10      # pass
expect 10 to lt 5      # fail
```

#### gte - Greater Than or Equal

```simple
expect value to gte other
expect 10 to gte 10    # pass
expect 10 to gte 5     # pass
expect 5 to gte 10     # fail
```

#### lte - Less Than or Equal

```simple
expect value to lte other
expect 5 to lte 5      # pass
expect 5 to lte 10     # pass
expect 10 to lte 5     # fail
```

### Collection Matchers

#### include - Contains Element

```simple
expect collection to include value
expect [1, 2, 3] to include 2
expect [1, 2, 3] to include 5      # fail
expect "hello" to include "l"      # strings work too
```

#### have_length / have_size - Collection Length

```simple
expect collection to have_length size
expect [1, 2, 3] to have_length 3
expect [1, 2, 3] to have_size 3    # alias
expect [] to have_length 0
expect "hello" to have_length 5
```

#### be_empty - Empty Collection

```simple
expect collection to be_empty
expect [] to be_empty
expect {} to be_empty
expect "" to be_empty
expect [1] to be_empty             # fail
```

### String Matchers

#### include_string - Contains Substring

```simple
expect string to include_string substring
expect "hello world" to include_string "world"
expect "hello world" to include_string "xyz"   # fail
```

#### start_with - String Prefix

```simple
expect string to start_with prefix
expect "hello world" to start_with "hello"
expect "hello" to start_with "bye"             # fail
```

#### end_with - String Suffix

```simple
expect string to end_with suffix
expect "hello world" to end_with "world"
expect "hello" to end_with "bye"               # fail
```

#### be_blank - Blank/Empty String

```simple
expect string to be_blank
expect "" to be_blank
expect "   " to be_blank
expect "\n\t" to be_blank
expect "hello" to be_blank                     # fail
```

### Error Matchers

#### expect_raises - Exception Handling

With specific error type:
```simple
expect_raises ErrorType:
    risky_operation()

expect_raises ValueError:
    raise ValueError("invalid")
```

Any error:
```simple
expect_raises:
    operation_that_might_fail()

expect_raises:
    1 / 0
```

### Negation

Use `not_to` to negate any matcher:

```simple
expect value not_to eq expected
expect 5 not_to eq 6
expect [1, 2, 3] not_to include 5
expect "hello" not_to start_with "bye"
expect [1] not_to be_empty
```

### Matcher Summary Table

| Category | Matchers |
|----------|----------|
| Equality | eq, be, be_nil |
| Comparison | gt, lt, gte, lte |
| Collections | include, have_length, have_size, be_empty |
| Strings | include_string, start_with, end_with, be_blank |
| Errors | expect_raises |

All matchers support negation with `not_to`.

### Custom Matchers

Extend with custom matchers by implementing the Matcher trait:

```simple
class BeDivisibleByMatcher:
    divisor: Int

impl Matcher[Int] for BeDivisibleByMatcher:
    fn match(self, actual: Int) -> MatchResult:
        if actual % self.divisor == 0:
            return MatchResult.success()
        else:
            return MatchResult.failure(
                "Expected ${actual} to be divisible by ${self.divisor}"
            )

fn be_divisible_by(divisor: Int) -> BeDivisibleByMatcher:
    return BeDivisibleByMatcher { divisor: divisor }

# Usage
expect 12 to be_divisible_by 3     # pass
expect 13 to be_divisible_by 3     # fail
```

---

## Gherkin-Style Syntax

### Overview

Simple supports Gherkin-style BDD syntax for system tests with `feature`, `scenario`, and `examples` tables.

### Example

```simple
examples addition:
    """Test data for basic addition operations"""
    a    b    result
    1    2    3
    10   20   30
    -5   10   5
    0    0    0

feature Basic Calculator Operations:
    """Core operations on a fresh calculator"""

    scenario outline Adding two numbers:
        """Add <a> then <b>, expect <result>"""
        given fresh calculator:
        when add <a>:
        when add <b>:
        then value is <result>:

        examples addition:
```

### Syntax Reference

#### Keywords

| Form | Meaning |
|------|---------|
| `examples name:` | Named examples table (two-space delimiter) |
| `context pattern:` | Step definition with `<placeholder>` support |
| `feature name:` | Feature grouping |
| `scenario name:` | Single test case |
| `scenario outline name:` | Parameterized test with examples |
| `given/when/then/and_then pattern:` | Step references |
| `"""..."""` | Doc comment (any level) |
| `${examples name}` | Embed table in documentation |

#### Two-Space Delimiter

Examples tables use **two or more spaces** as column delimiter:

```
start  operation       result    # header row
10     add 5           15        # "add 5" is single value (one space)
10     multiply by 2   20        # "multiply by 2" is single value
```

- Single space → part of value
- Two+ spaces → column boundary

#### Context Definitions

```simple
context fresh calculator:
    """A new calculator instance with value 0"""
    calc = Calculator.new()

context calculator at <n>:
    """Calculator initialized with value <n>"""
    calc = Calculator.new().set(n)

context add <n>:
    """Add <n> to current value"""
    calc = calc.add(n)

context value is <n>:
    """Assert current value equals <n>"""
    calc.value == n
```

### Grammar (EBNF)

```ebnf
(* === BDD CONSTRUCTS === *)

examples_stmt = 'examples' IDENT ':' NEWLINE INDENT
                doc_comment?
                header_row
                data_row+
                DEDENT ;

context_stmt  = 'context' step_pattern ':' NEWLINE INDENT
                doc_comment?
                (statement | expr)+
                DEDENT ;

feature_stmt  = 'feature' description ':' NEWLINE INDENT
                doc_comment?
                scenario_stmt+
                DEDENT ;

scenario_stmt = 'scenario' 'outline'? description ':' NEWLINE INDENT
                doc_comment?
                step_ref+
                examples_ref?
                DEDENT ;

step_ref      = ('given' | 'when' | 'then' | 'and_then') step_pattern ':'
                (NEWLINE | INDENT block DEDENT) ;

examples_ref  = 'examples' IDENT? ':'
                (NEWLINE | INDENT inline_examples DEDENT) ;

(* === TWO-SPACE DELIMITED ROWS === *)

header_row    = value (TWO_SPACES value)* NEWLINE ;
data_row      = value (TWO_SPACES value)* NEWLINE ;

TWO_SPACES    = '  ' ' '* ;   (* 2+ consecutive spaces *)
```

### Implementation Status

| Component | Status |
|-----------|--------|
| Grammar spec | ✅ |
| Parser keywords | ✅ |
| Runtime functions | ✅ |
| Step pattern matching | ✅ |
| Examples tables | ✅ |
| Scenario outline | ✅ |
| Two-space lexer mode | 📋 |
| Examples interpolation | 📋 |
| Living doc generation | ✅ |

---

## Runner & CLI

### Discovery

Default pattern: `test/**/*_spec.spl`

Layer selection:
- `--unit` → test/unit
- `--integration` → test/integration
- `--system` → test/system
- `--all` → entire test/

### Filtering

```bash
simple test --tag slow
simple test --skip-tag db
simple test --match "Stack when empty"
simple test --fail-fast
simple test --seed 12345
```

### Output Formatters

- `progress` - dots
- `doc` - nested describe/context output
- `json` - IDE integration

### Exit Codes

| Code | Meaning |
|------|---------|
| 0 | All pass |
| 1 | Test failures |
| 2 | Environment/bootstrap failure |
| 3 | Invalid config/discovery error |

---

## Coverage Policy

### Definitions

**Public function:** Top-level exported function from module.

**Public type:** Exported class or struct.

**Logic-containing type:** Public type with non-trivial behavior (has methods beyond constructors/getters). Mark with `@logic` or `@dto` for explicitness.

### Thresholds

| Layer | Metric | Target |
|-------|--------|--------|
| Integration | Public function touch | 100% |
| Integration | Public function lines | ≥80% (optional) |
| System | Public type touch | 100% |
| System | Public method touch | ≥80% (optional) |

Exceptions via attributes: `@no_system_test_required`, `@experimental`

### Implementation

1. **Symbol inventory:** Compiler emits `symbols.json` with function/type ranges
2. **Execution data:** LLVM coverage regions or interpreter trace points
3. **Attribution:** Map executed ranges to symbols

Report outputs:
- `coverage_api.json` - machine-readable
- Console summary - missing functions/types

---

## Best Practices

### Do

- Name clearly: `it "adds two positive numbers":` not `it "works":`
- One assertion concept per test
- Use context sharing for reusable fixtures
- Mark Given-When-Then with comments
- Use `given_lazy` for test data, `given:` for setup

### Don't

- Multiple behaviors per test
- Test implementation details
- Share mutable state between tests
- Use vague test names
- Skip without marking `pending`

### Test Organization

#### Naming Conventions

- Files: `feature_spec.spl`
- Describe: `describe "ClassName":`
- Context: `context "when condition":`
- Test: `it "does something":`

#### Test Levels

**Unit** - Fast, isolated:
```simple
describe "Parser":
    it "parses tokens":
        expect Parser.parse("1 + 2") != nil
```

**Integration** - Module boundaries:
```simple
describe "Database":
    before_all:
        db.connect()

    it "queries work":
        expect db.query("SELECT 1") != nil
```

**System** - End-to-end:
```simple
describe "API Server":
    before_all:
        start_server()

    it "handles requests":
        expect api.get("/health").status == 200
```

---

## Examples

### Unit Test

```simple
import test.unit.*

describe "Parser::tokenize":
    it "splits identifiers":
        toks = Parser.tokenize("abc def")
        expect toks to eq ["abc", "def"]
```

### Integration Test

```simple
import test.integration.*
import mypkg.api.*

describe "mypkg.api":
    it "parses config":
        cfg = parse_config("x=1")
        expect cfg.x to eq 1
```

### System Test

```simple
import test.system.*
import mypkg.*

describe "AuthService":
    before_each:
        env = test_env_real()
        svc = AuthService.new(env)

    it "logs in valid user":
        user = User.new(name: "a", token: "ok")
        expect svc.login(user) to eq Ok
```

### Setup Once, Use Multiple Times

```simple
context_def :api_client:
    given_lazy :client, \:
        APIClient.new()

describe "API":
    context :api_client:
        it "test 1":
            expect client != nil

        it "test 2":
            expect client != nil
```

### Test Data Variants

```simple
context_def :empty_list:
    given_lazy :items, \: []

context_def :filled_list:
    given_lazy :items, \: [1, 2, 3]

describe "List":
    context :empty_list:
        it "is empty":
            expect items.len() == 0

    context :filled_list:
        it "has items":
            expect items.len() == 3
```

### Composed Setup

```simple
context_def :database:
    given:
        db.connect()

context_def :fixtures:
    given:
        load_fixtures()

context_def :auth:
    given_lazy :token, \: "xyz"

describe "Integration":
    context_compose :database, :fixtures, :auth:
        it "full setup works":
            expect true
```

### Environment Helpers

#### bootstrap.spl

```simple
# test/environment/bootstrap.spl
fn setup_test_env():
    create_temp_workspace()
    set_env("TEST_TMP", temp_dir())
    set_env("TEST_SEED", random_seed())
```

#### Fixtures

```
test/environment/fixtures/
  files/
  datasets/
  golden/
```

Helpers:

```simple
fixture_path("x.json")
golden_read("stack/output.txt")
golden_assert(actual, "stack/output.txt")
```

#### Timeouts

```simple
timeout_default(5000)

with_timeout 10_000:
    slow_operation()
```

---

## Troubleshooting

### Fixture not available

**Problem:**
```simple
context "test":
    it "uses user":
        expect user.name == "Alice"  # Error: user undefined
```

**Solution:**
```simple
context "test":
    given_lazy :user, \:
        { name: "Alice" }

    it "uses user":
        expect user.name == "Alice"
```

### Context not found

**Problem:**
```simple
context :undefined_context:  # Error: not found
    it "fails":
        expect true
```

**Solution:**
```simple
context_def :my_context:
    given_lazy :value, \: 42

context :my_context:
    it "works":
        expect value == 42
```

### State leaking between tests

**Problem:**
```simple
context "test":
    let x = 0

    it "modifies x":
        x = 5
        expect x == 5

    it "should be fresh":
        expect x == 0  # Fails: x is still 5
```

**Solution:**
```simple
context "test":
    given:
        x = 0

    it "modifies x":
        x = 5
        expect x == 5

    it "is fresh":
        expect x == 0  # Passes: fresh setup
```

---

## See Also

- [Doctest](sdoctest.md) - Documentation testing framework
- [Mock Framework](mock.md) - Test doubles and mocking
- [SDN](sdn.md) - Table syntax used in examples
