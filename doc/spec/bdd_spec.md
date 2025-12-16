Simple BDD Spec Framework

A Ruby/RSpec-style BDD test framework for Simple, using indentation blocks, optional call parentheses, and optional let.

This document defines:

1. the test folder taxonomy (test/unit, test/integration, test/system, test/environment)


2. default imports and directory conventions


3. the BDD DSL (RSpec-like) and execution semantics


4. public-API coverage rules and how to compute/report them



RSpec alignment references: hook scopes (:example, :context, :suite), shared examples, matcher protocol, and block expectations. 


---

1) Folder layout and intent

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

1.1 test/ (root)

Goal: provide a consistent “test language environment”.

Sets default imports: std.* and std.spec.*

Defines shared helpers used by all test layers (assertions, matchers, timeouts, logging, common fakes)


1.2 test/environment/

Goal: own test runtime orchestration.

Process-level bootstrap (env vars, temp dirs, ports)

Fixtures and external dependencies (DB containers, mock servers, GPU presence checks, etc.)

Global configuration for the spec runner (formatter, seed, tag defaults)


1.3 test/unit/

Goal: fast, isolated tests for internal behavior.

Targets: private/internal functions, pure logic units, small modules

Fakes/mocks encouraged

Coverage target: Branch/condition coverage (merged with environment tests)


1.4 test/integration/

Goal: validate public functions and module boundaries.

Targets: exported functions and “module-level” APIs

Uses real dependencies where feasible, but still avoids end-to-end orchestration

Coverage target: Public Function Touch (100%) - ensures all public functions are called at least once


1.5 test/system/

Goal: validate public types (class/struct) and end-to-end behavior flows.

Targets: public classes/structs that contain business logic (“logic-containing types”)

Runs with realistic environment (filesystem, network, processes) via test/environment

Coverage target: Public Class/Struct Touch (100%) - ensures all public classes/structs are used at least once


This layered structure matches practical guidance from the “test pyramid” concept: more unit tests, fewer system tests, to balance confidence and cost. 


---

2) Default imports via __init__.spl

2.1 test/__init__.spl (default imports for all test code)

Contract: any file under test/ implicitly gets:

import std.*

import std.spec.*

optional: common helpers (timeouts, temp dirs, golden files)


Example:

# test/__init__.spl
import std.*
import std.spec.*
import test.environment.*        # expose bootstrap + helpers (optional)

2.2 Per-layer __init__.spl

Use these to:

set defaults (tags, timeouts)

provide layer-specific helper functions


Example:

# test/system/__init__.spl
import test.*                    # inherits std + spec
tag_default :system
timeout_default 30_000


---

3) BDD DSL (indent blocks, parentheses optional)

3.1 Example groups

describe "Stack":
  context "when empty":
    it "raises on pop":
      expect_raises EmptyStack:
        Stack.new.pop

3.2 Hooks (RSpec-aligned semantics)

Support:

before_each: / after_each: (RSpec :example default) 

before_all: / after_all: (RSpec :context) 

optional before_suite: / after_suite: (RSpec :suite) 


Hook ordering:

before_all: outer → inner, once per group

before_each: outer → inner, per example

after_each: inner → outer, per example

after_all: inner → outer, once per group


3.3 let is optional

Use plain locals if you prefer explicitness.

let is a convenience for memoized per-example state.


Both are valid:

describe "A":
  before_each:
    x = make_x()

  it "works":
    expect x.value to eq 1

describe "A":
  let x = make_x()

  it "works":
    expect x.value to eq 1

3.4 Expectations + matchers

Value expectations:

expect actual to eq expected
expect actual not_to eq expected

Block expectations (indent-native form):

expect_raises SomeError:
  do_something()

This corresponds to RSpec’s block expectations (expect { ... }.to raise_error) and requires “block expectation” support in matcher protocol terms. 

3.5 Shared examples

shared_examples "a stack-like container":
  it "supports push/pop":
    s = make()
    s.push 1
    expect s.pop to eq 1

describe "Stack":
  fn make() -> Stack:
    return Stack.new
  it_behaves_like "a stack-like container"

Shared example groups are stored and only realized when included in another group (RSpec behavior).


3.6 Reusable Contexts (Context Sharing)

**Overview:** Define reusable setup/fixture groups once, compose them across multiple tests.

**Syntax:**

```simple
# Define a named, reusable context_def (lowercase)
context_def :as_admin:
    given_lazy :user, \:
        create(:user, :admin)

    given:
        login_as(user)

context_def :with_database:
    given:
        db = Database.connect(:test)
        db.migrate()

describe "AdminDashboard":
    # Reference a context_def by symbol
    context :as_admin:
        it "shows admin panel":
            expect page.has_selector?(".admin-panel")

    # Compose multiple contexts (mix-in semantics)
    context_compose :as_admin, :with_database:
        it "loads from database":
            expect user.data.persisted?

    # Inline context (anonymous) with inline given
    context "when user logs out":
        given:
            logout_as(user)

        it "shows login form":
            expect page.has_selector?(".login-form")

    # Mix: reference context_def + extend with inline given
    context :as_admin:
        given_lazy :extra_perms, \:
            :super

        it "has extra permissions":
            expect user.permissions.includes?(extra_perms)
```

**Keywords:**

| Keyword | Purpose | Semantics |
|---------|---------|-----------|
| `context_def :name:` | Define reusable context | Global singleton (stored in registry) |
| `context :symbol:` | Reference named context_def | Mix-in: runs all givens from that context |
| `context_compose :a, :b:` | Compose multiple contexts | Sequential: :a givens run, then :b givens |
| `context "string":` | Anonymous context | Nested describe (nested group) |
| `given_lazy :name, \: ...` | Lazy fixture (memoized) | Evaluated once per example, cached |
| `given :name, \: ...` | Named eager fixture | Runs before each example (not memoized) |
| `given:` | Unnamed eager setup | Runs before each example (like before_each) |
| `then { }` | BDD-style assertion | Optional - synonym for truthy check |

**Semantics:**

- **context_def definition** is stored globally (name registered in context registry)
- **context reference** `:symbol:` looks up definition and runs all givens from that context
- **context_compose** composes multiple contexts in order: context A givens run, then context B givens
- **given_lazy** creates memoized fixture (stored per example, cleared after example)
- **given :name** runs eagerly before each example with clear documentation
- **given:block** runs eagerly before each example (like before_each hook)
- **then** is optional sugar for common BDD pattern

**BDD "Given-When-Then" Pattern:**

```simple
context_def :empty_stack:
    # Given: initial state
    given_lazy :stack, \:
        Stack.new

describe "Stack":
    context :empty_stack:
        # Scenario: push operation
        context "when pushed":
            # When: perform action
            given:
                stack.push(42)

            # Then: verify results
            it "size increases":
                expect stack.size == 1

            it "top is correct":
                expect stack.top == 42

        # Scenario: pop operation
        context "when popped":
            # When: setup state
            given:
                stack.push(99)
                stack.push(42)

            # Then: verify behavior
            it "pops correct value":
                expect stack.pop == 42

            it "size decreases":
                expect stack.size == 1
```

**Sequential Given Block Example (Contexts + Variables):**

```simple
context_def :user_data:
    given_lazy :user, \:
        { name: "Alice", id: 42 }

context_def :db_setup:
    given:
        db.connect()
        db.migrate()

describe "Integrated Setup":
    context "with sequential given":
        # Single given: block with multiple sequential steps
        given:
            # Step 1: Apply database setup context
            given :db_setup

            # Step 2: Apply user fixtures context
            given :user_data

            # Step 3: Define derived variables
            let user_key = "user_" + user.id.to_string()
            let greeting = "Welcome, " + user.name

        it "has user from context":
            expect user.name == "Alice"

        it "has derived variables":
            expect user_key == "user_42"
            expect greeting == "Welcome, Alice"
```

**Fixture Composition Example:**

```simple
context_def :setup_a:
    given_lazy :x, \:
        10

context_def :setup_b:
    given_lazy :y, \:
        x + 5  # y depends on x (when composed after :setup_a)

describe "Test":
  context :setup_a, :setup_b do
    given(:z) { y * 2 }

    it "composes in order":
      # x = 10 (from :setup_a)
      # y = 15 (from :setup_b, uses x)
      # z = 30 (from inline, uses y)
      expect z == 30
end
```

**Future considerations (edge cases):**

- Context inheritance: `Context :admin < :user do` (extend a Context)
- Parameterized Contexts: `Context :with_role do |role|` (pass arguments)
- Context composition operators: `context :a & :b` (merge), `context :a | :b` (choose)


---

4) Runner behavior and CLI

4.1 Discovery

Default: test/**/_spec.spl or test/**/*_spec.spl (choose one convention; recommend *_spec.spl)

Layer selection:

--unit → test/unit

--integration → test/integration

--system → test/system

--all → entire test/



4.2 Filtering

--tag slow, --skip-tag db

--match "Stack when empty" (substring or regex)

--fail-fast

--seed N (deterministic shuffle)


4.3 Output / formatters

progress (dots)

doc (nested describe/context output)

json (for IDE integration)


4.4 Exit codes

0 all pass

1 test failures

2 environment/bootstrap failure

3 invalid config / discovery errors



---

5) Coverage policy by test layer

You requested coverage rules that explicitly target public API:

test/system/ checks public class/struct coverage (logic-containing types)

test/integration/ checks public function coverage

test/unit/ is unconstrained (may target internals), but still contributes to line/branch totals


5.1 Definitions

Public function
A top-level exported function (visibility public and exported from module).

Public type
A public class or struct exported from module.

Logic-containing type
A public type that contains non-trivial behavior. Choose one:

Explicit attribute: @logic / @dto / @pure_data

Heuristic fallback: has ≥1 public method with a non-empty body (beyond constructors/getters)


5.2 Required coverage thresholds (recommended defaults)

Integration (public functions)

Public Function Touch Coverage: 100%

every exported public function must be executed by at least one integration test


Optional: Public Function Line Coverage: ≥ 80% (within the function body)


System (public types)

Public Type Touch Coverage: 100% for logic-containing public types

each public logic type must have at least one system test that instantiates and exercises it


Optional: Public Method Touch Coverage: ≥ 80% across public methods of those types


You can allow exceptions via tags/metadata:

@no_system_test_required (for DTOs)

@experimental (excluded unless --include-experimental)


5.3 How to implement “public API coverage” reporting

To report “public function/type coverage”, you need a mapping:

1. Exported symbol inventory (public API list)


2. Executed source ranges (coverage)


3. Range-to-symbol attribution



(1) Exported symbol inventory

At compile time, emit symbols.json (or symbols.smf) containing:

symbol id, kind (fn, class, struct, method)

visibility (public/private)

source file + start/end range

tags/attributes (@logic, @dto, etc.)



(2) Executed source ranges Use whichever your toolchain supports:

LLVM-style coverage regions (recommended if Simple lowers to LLVM IR)

VM/interpreter trace points (if running interpreted tests)

Hybrid: line-hit bitmap + region detail


(3) Attribution algorithm

For each symbol S with source range [start,end]:

touched(S) = any executed region overlaps [start,end]

line_coverage(S) = executed_lines_in_range / total_lines_in_range


Then compute:

Public Function Touch Coverage = touched(public fn)/count(public fn)

Public Type Touch Coverage = touched(public logic type)/count(public logic type)

Public Method Touch Coverage = touched(public methods)/count(public methods)



Reporting

Print a summary at end of run, plus a machine-readable coverage_api.json:

missing public functions (integration)

missing public logic types (system)

optional per-symbol coverage %




---

6) Predefined helpers in test/environment/

Recommended baseline modules:

6.1 test/environment/bootstrap.spl

Responsibilities:

create temp workspace

set env vars (TEST_TMP, TEST_SEED)

choose ports / start dependent services

register global spec config (formatters, default tags)


6.2 Fixtures

test/environment/fixtures/
  files/
  datasets/
  golden/

Provide helpers:

fixture_path "x.json"

golden_read "stack/output.txt"

golden_assert actual, "stack/output.txt"


6.3 Timeouts and isolation

timeout_default ms

with_timeout ms: ...

optional: per-test process isolation for system tests



---

7) Concrete examples by layer

7.1 Unit test (internal behavior)

import test.unit.*

describe "Parser::tokenize":
  it "splits identifiers":
    toks = Parser.tokenize "abc def"
    expect toks to eq ["abc","def"]

7.2 Integration test (public functions)

import test.integration.*
import mypkg.api.*

describe "mypkg.api":
  it "public: parse_config":
    cfg = parse_config "x=1"
    expect cfg.x to eq 1

7.3 System test (public types)

import test.system.*
import mypkg.*

describe "AuthService":
  before_each:
    env = test_env_real()     # from test/environment
    svc = AuthService.new env

  it "logs in valid user":
    user = User.new name="a", token="ok"
    expect svc.login(user) to eq Ok


---

8) Deliverables to add to the Simple repo

1. doc/spec/bdd_spec.md (this document)


2. std/spec/ implementation modules:

dsl, registry, runtime, expect, matchers/*, runner/cli, formatter/*



3. Test skeleton:

test/__init__.spl

test/environment/bootstrap.spl

test/unit/__init__.spl, etc.



4. Coverage integration:

symbols.json emitter in compiler

coverage_api.json report in runner





---

If you want, I can also provide:

a canonical doc/spec/bdd_spec.md file body ready to commit (with section numbering, glossary, and CLI reference), and

a minimal std/spec module skeleton (files + pseudocode) that implements registration, hook ordering, and the public-API coverage report.
