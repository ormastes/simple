# Simple BDD Spec Framework

A Ruby/RSpec-style BDD test framework for Simple, using indentation blocks and optional parentheses.

## Contents

1. [Folder Layout](#1-folder-layout)
2. [Default Imports](#2-default-imports)
3. [BDD DSL](#3-bdd-dsl)
4. [Runner & CLI](#4-runner--cli)
5. [Coverage Policy](#5-coverage-policy)
6. [Environment Helpers](#6-environment-helpers)
7. [Examples by Layer](#7-examples-by-layer)

---

## 1. Folder Layout

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

### 1.1 test/ (root)

Provides the test language environment with default imports (`std.*`, `std.spec.*`) and shared helpers (matchers, timeouts, fakes).

### 1.2 test/environment/

Owns test runtime orchestration:
- Process-level bootstrap (env vars, temp dirs, ports)
- External dependencies (DB containers, mock servers)
- Global spec runner configuration

### 1.3 test/unit/

Fast, isolated tests for internal behavior.
- Targets: private functions, pure logic, small modules
- Fakes/mocks encouraged
- Coverage: branch/condition

### 1.4 test/integration/

Validates public functions and module boundaries.
- Targets: exported functions, module-level APIs
- Uses real dependencies where feasible
- Coverage: 100% public function touch

### 1.5 test/system/

Validates public types and end-to-end flows.
- Targets: public classes/structs with business logic
- Runs with realistic environment via test/environment
- Coverage: 100% public type touch

This follows the test pyramid pattern: more unit tests, fewer system tests.

---

## 2. Default Imports

### 2.1 test/__init__.spl

All files under `test/` implicitly receive:

```simple
import std.*
import std.spec.*
import test.environment.*  # optional
```

### 2.2 Per-layer __init__.spl

Set layer-specific defaults:

```simple
# test/system/__init__.spl
import test.*
tag_default :system
timeout_default 30_000
```

---

## 3. BDD DSL

### 3.1 Example Groups

```simple
describe "Stack":
    context "when empty":
        it "raises on pop":
            expect_raises EmptyStack:
                Stack.new().pop()
```

### 3.2 Hooks

| Hook | Scope | Runs |
|------|-------|------|
| `before_each:` | per example | outer → inner |
| `after_each:` | per example | inner → outer |
| `before_all:` | per group | once, outer → inner |
| `after_all:` | per group | once, inner → outer |

### 3.3 Fixtures

**let** - Memoized per-example (optional convenience):

```simple
describe "A":
    let x = make_x()

    it "works":
        expect x.value to eq 1
```

**before_each** - Explicit setup:

```simple
describe "A":
    before_each:
        x = make_x()

    it "works":
        expect x.value to eq 1
```

### 3.4 Expectations

**Value expectations:**

```simple
expect actual to eq expected
expect actual not_to eq expected
```

**Block expectations:**

```simple
expect_raises SomeError:
    do_something()
```

### 3.5 Shared Examples

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

### 3.6 Context Sharing

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
            expect page.has_selector?(".admin-panel")

    context_compose :as_admin, :with_database:
        it "loads from database":
            expect user.data.persisted?
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

**Fixture Composition:**

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

**Sequential Given Block:**

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

## 4. Runner & CLI

### 4.1 Discovery

Default pattern: `test/**/*_spec.spl`

Layer selection:
- `--unit` → test/unit
- `--integration` → test/integration
- `--system` → test/system
- `--all` → entire test/

### 4.2 Filtering

```bash
simple test --tag slow
simple test --skip-tag db
simple test --match "Stack when empty"
simple test --fail-fast
simple test --seed 12345
```

### 4.3 Output Formatters

- `progress` - dots
- `doc` - nested describe/context output
- `json` - IDE integration

### 4.4 Exit Codes

| Code | Meaning |
|------|---------|
| 0 | All pass |
| 1 | Test failures |
| 2 | Environment/bootstrap failure |
| 3 | Invalid config/discovery error |

---

## 5. Coverage Policy

### 5.1 Definitions

**Public function:** Top-level exported function from module.

**Public type:** Exported class or struct.

**Logic-containing type:** Public type with non-trivial behavior (has methods beyond constructors/getters). Mark with `@logic` or `@dto` for explicitness.

### 5.2 Thresholds

| Layer | Metric | Target |
|-------|--------|--------|
| Integration | Public function touch | 100% |
| Integration | Public function lines | ≥80% (optional) |
| System | Public type touch | 100% |
| System | Public method touch | ≥80% (optional) |

Exceptions via attributes: `@no_system_test_required`, `@experimental`

### 5.3 Implementation

1. **Symbol inventory:** Compiler emits `symbols.json` with function/type ranges
2. **Execution data:** LLVM coverage regions or interpreter trace points
3. **Attribution:** Map executed ranges to symbols

Report outputs:
- `coverage_api.json` - machine-readable
- Console summary - missing functions/types

---

## 6. Environment Helpers

### 6.1 bootstrap.spl

```simple
# test/environment/bootstrap.spl
fn setup_test_env():
    create_temp_workspace()
    set_env("TEST_TMP", temp_dir())
    set_env("TEST_SEED", random_seed())
```

### 6.2 Fixtures

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

### 6.3 Timeouts

```simple
timeout_default(5000)

with_timeout 10_000:
    slow_operation()
```

---

## 7. Examples by Layer

### 7.1 Unit Test

```simple
import test.unit.*

describe "Parser::tokenize":
    it "splits identifiers":
        toks = Parser.tokenize("abc def")
        expect toks to eq ["abc", "def"]
```

### 7.2 Integration Test

```simple
import test.integration.*
import mypkg.api.*

describe "mypkg.api":
    it "parses config":
        cfg = parse_config("x=1")
        expect cfg.x to eq 1
```

### 7.3 System Test

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

---

## See Also

- [Spec Framework Guide](spec_framework_guide.md)
- [Matchers Reference](spec_matchers_reference.md)
