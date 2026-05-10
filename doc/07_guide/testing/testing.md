# Testing Guide

Complete guide to testing in Simple: the SPipe BDD framework, matchers, mocking, fixtures, context sharing, test database, platform organization, and test policy.

---

## Table of Contents

1. [SPipe Framework](#spipe-framework)
2. [BDD DSL Syntax](#bdd-dsl-syntax)
3. [Matchers Reference](#matchers-reference)
4. [Hooks](#hooks)
5. [Fixtures and Setup](#fixtures-and-setup)
6. [Context Sharing](#context-sharing)
7. [Shared Examples](#shared-examples)
8. [Tags and Filtering](#tags-and-filtering)
9. [Gherkin-Style Syntax](#gherkin-style-syntax)
10. [Mocking](#mocking)
11. [Test Helpers](#test-helpers)
12. [Test Policy and Levels](#test-policy-and-levels)
13. [Test Database](#test-database)
14. [Platform Organization](#platform-organization)
15. [Runner and CLI](#runner-and-cli)
16. [UI System Testing](#ui-system-testing)
17. [Best Practices](#best-practices)
18. [Troubleshooting](#troubleshooting)

---

## SPipe Framework

SPipe is a BDD (Behavior-Driven Development) testing framework for Simple, inspired by RSpec. It combines executable tests with embedded markdown documentation via triple-quoted strings.

### Quick Start

```simple
use std.spipe.*

describe "Calculator":
    context "addition":
        it "adds two numbers":
            expect(2 + 2).to_equal(4)

        it "adds negatives":
            expect(5 + (-3)).to_equal(2)
```

Run tests:

```bash
simple test                           # Run all tests
simple test path/to/spec.spl          # Run specific test
simple test --tag slow                # Run tests with tag
```

### File Structure

Test files follow these patterns:
- `*_spec.spl` -- BDD spec files (preferred)
- `*_test.spl` -- Test files

Directory layout:

```
test/
  unit/           # Fast, isolated tests
  integration/    # Module boundary tests
  system/         # End-to-end tests
  feature/        # CLI/tool and language feature tests
  shared/         # Cross-platform tests (host + baremetal)
```

### Test Pyramid

- **Unit** -- Fast, isolated tests for internal behavior (private functions, pure logic)
- **Integration** -- Validates public functions and module boundaries
- **System** -- End-to-end flows with realistic environment

---

## BDD DSL Syntax

### describe

Creates a top-level example group:

```simple
describe "UserService":
    it "creates a user":
        val user = UserService.create("alice")
        expect(user.name).to_equal("alice")
```

### context

Creates nested groups for different scenarios:

```simple
describe "User":
    context "when logged in":
        it "shows dashboard":
            # test code

    context "when logged out":
        it "shows login form":
            # test code
```

### it

Defines a single test example:

```simple
describe "Array":
    it "returns length":
        expect([1, 2, 3].len()).to_equal(3)

    it "can be empty":
        expect([].is_empty()).to_equal(true)
```

### skip

Skip a test temporarily:

```simple
describe "Feature":
    skip "pending implementation":
        nil
```

### SPipe Document Format

Embed markdown documentation in test files using triple-quoted strings. The `simple spipe-docgen` command extracts these blocks and generates markdown documentation in `doc/spec/`.

Optional metadata fields `**Artifacts:**`, `**Screenshots:**`, `**TUI Captures:**`, and `**Logs:**` let a spec publish evidence links into the generated markdown. List multiple items inline with `;` or `,`, or place them on bullet lines directly below the field.
If those fields are omitted, `spipe-docgen` will also auto-discover evidence under the standard screenshot tree `doc/spec/image/<spec-relative-path>/` when files already exist there.
The generated Evidence section now renders a compact category summary plus per-category tables with item name, evidence kind, and path. For non-image evidence, prefer `build/test-artifacts/<spec-relative-path>/` so logs, ANSI captures, JSON summaries, and text artifacts can be discovered automatically too.
For CI/publication, use `simple spipe-docgen ... --output docs/spec` when you want a publishable static-doc tree under `docs/`. The `simple test --doc` flow writes summary pages to `docs/test-spec.md` and `docs/test-spec.html`, and also regenerates `docs/spec/` for the specs that were executed. Evidence roots stay separate: screenshots under `doc/spec/image/` and non-image evidence under `build/test-artifacts/`.

```simple
"""
# Feature Name Specification

**Status:** Complete | In Progress | Draft
**Feature IDs:** #XXX
**Keywords:** keyword1, keyword2

## Overview
Brief description.
"""

describe "Feature":
    """
    ## Feature Category
    Detailed description for this section.
    """

    context "when condition":
        it "does expected behavior":
            expect(true).to_equal(true)
```

Status values: `Stable`, `Implementing`, `Draft`, `Planned`.

---

## Matchers Reference

**Built-in matchers only.** Do not use custom matchers.

### Equality and Identity

```simple
expect(value).to_equal(expected)     # Equality
expect(obj).to_be(same_obj)          # Identity
expect(result).to_be_nil()           # Nil check
```

### Comparison

```simple
expect(5).to_be_greater_than(3)
expect(3).to_be_less_than(5)
```

### Collection and String

```simple
expect([1, 2, 3]).to_contain(2)
expect("hello world").to_contain("world")
expect("hello").to_start_with("hel")
expect("hello").to_end_with("lo")
```

### Boolean

Use `to_equal(true)` -- not `to_be_true()`.

```simple
expect(user.is_valid()).to_equal(true)
```

---

## Hooks

| Hook | Scope | Runs |
|------|-------|------|
| `before_each:` | per example | outer -> inner |
| `after_each:` | per example | inner -> outer |
| `before_all:` | per group | once, outer -> inner |
| `after_all:` | per group | once, inner -> outer |

```simple
describe "Database":
    before_each:
        setup_database()

    after_each:
        cleanup()

    it "inserts records":
        # test with db available
```

---

## Fixtures and Setup

### Lazy Fixtures

Memoized once per example:

```simple
context "with user":
    given_lazy :user, \:
        { name: "Alice", id: 42 }

    it "accesses user":
        expect user.name == "Alice"
```

### Named Eager Setup

Runs before each example (not memoized):

```simple
context "complex setup":
    given :db_connect, \:
        database.connect()

    it "has setup":
        expect true
```

### Unnamed Eager Setup

```simple
context "setup":
    given:
        setup_database()

    it "works":
        expect true
```

### Fixture Types and BDD Pattern

| Type | Syntax | BDD Role | Timing |
|------|--------|----------|--------|
| Unnamed eager | `given { ... }` | When (setup) | Before each example |
| Named eager | `given :name, \: ...` | When (named action) | Before each example |
| Named lazy | `given_lazy :name, \: ...` | Given (state) | Per example (memoized) |

Execution order: lazy fixtures memoized, then named `given` blocks in order, then unnamed `given` blocks, then `it` block. Fresh state for each example.

### Inline Lazy Fixtures

`given_lazy` works in both `context_def` definitions and regular `context` blocks:

```simple
describe "User Service":
    context "with authenticated user":
        given_lazy :user, \:
            { id: 42, email: "user@example.com", role: "admin" }

        it "has user email":
            expect user.email == "user@example.com"
```

---

## Context Sharing

Define reusable setup groups that can be referenced across multiple test suites.

### Define a Reusable Context

```simple
context_def :as_admin:
    given_lazy :user, \:
        create(:user, :admin)
```

### Reference a Context

```simple
describe "AdminDashboard":
    context :as_admin:
        it "shows admin panel":
            expect page.has_selector(".admin-panel")
```

### Compose Multiple Contexts

```simple
context_compose :as_admin, :with_database:
    it "loads from database":
        expect user.data.is_persisted()
```

### Sequential Given Blocks

Combine context references and variable definitions in a single `given:` block:

```simple
describe "Integrated Setup":
    context "with sequential given block":
        given:
            given :db_setup
            given :user_data
            let user_key = "user_" + user.id.to_string()

        it "has derived variables":
            expect user_key == "user_42"
```

### When to Use context_def vs Inline

| Scenario | Use |
|----------|-----|
| Fixtures used in 1 test suite | Inline `given_lazy` |
| Fixtures used in 3+ test suites | `context_def` + `context :name` |
| Complex setup with multiple steps | `context_def` + `given` |
| Composing fixtures | `context_compose` |

---

## Shared Examples

Reuse test examples across multiple contexts:

```simple
shared_examples "a collection":
    it "has a length":
        expect(subject.len()).to_be_greater_than(0)

describe "Array":
    val subject = [1, 2, 3]
    it_behaves_like "a collection"
```

---

## Tags and Filtering

### Adding Tags

```simple
# @slow
# @integration

describe "SlowTest":
    it "takes time":
        sleep(1000)
```

Or with decorator: `#[tag("slow")]`

### Running Tagged Tests

```bash
simple test --tag slow           # Run only @slow tests
simple test --tag integration    # Run only @integration tests
```

---

## Gherkin-Style Syntax

Simple supports Gherkin-style BDD for system tests:

```simple
examples addition:
    """Test data for addition"""
    a    b    result
    1    2    3
    10   20   30

feature Basic Calculator:
    scenario outline Adding two numbers:
        given fresh calculator:
        when add <a>:
        when add <b>:
        then value is <result>:
        examples addition:
```

Keywords: `examples`, `feature`, `scenario`, `scenario outline`, `given`, `when`, `then`, `and_then`.

---

## Mocking

**Library:** `std.testing.mock`

The mock library provides test doubles for verifying interactions with dependencies. It includes call tracking, verification, conditional returns, async mocking, and advanced scheduling.

### Basic Mock

```simple
import std.testing.mock as mock

val save_mock = mock.create_mock("save_user")
save_mock.record_call(["user123", "Alice"])

expect save_mock.was_called()
expect save_mock.call_count() == 1
expect save_mock.was_called_with(["user123", "Alice"])
```

### MockBuilder with Return Values

```simple
val mock = mock.MockBuilder.new("get_user")
    .returns(["Alice", "Bob", "Charlie"])

match mock.next_return_value():
    Some(v): print v  # "Alice"
    None: print "No more values"
```

### Mock Registry

Manage multiple mocks:

```simple
val registry = mock.MockRegistry.new()
registry.register("save", save_mock)
registry.register("load", load_mock)
registry.reset_all()
```

### Conditional Returns

```simple
val cond = mock.ConditionalReturns.new()
cond.add_condition(\args: args[0] == "admin", "admin_data")
cond.add_condition(\args: args[0] == "user", "user_data")
cond.set_default("guest_data")
```

### Behavior Sequences (State Machines)

```simple
val seq = mock.BehaviorSequence.new("disconnected")
seq.add_state("disconnected", "connecting...", Some("connecting"))
seq.add_state("connecting", "connected!", Some("connected"))
seq.add_state("connected", "ready", nil)
```

### Protocol Mock (Trait-like Interfaces)

```simple
val proto = mock.ProtocolMock.new()
proto.mock_method("authenticate", ["user", "pass"], "token_123")
val token = proto.record_method_call("authenticate", ["user", "pass"])
```

### Async Mocking

```simple
val async_mock = mock.AsyncMock.new("api_call")
async_mock.set_delay(100)
async_mock.set_return_values(["response1"])
val result = async_mock.record_async_call(["request"])
```

### Scheduling Utilities

- **TaskScheduler** -- Priority-based task execution
- **RetryPolicy** -- Configurable retry with backoff (exponential, linear)
- **RateLimiter** -- Simulate API rate limiting
- **TimeoutController** -- Handle async operation timeouts
- **Debouncer / Throttler** -- Control call frequency

### Mocking Best Practices

- Mock external dependencies only (database, HTTP, filesystem), not internal logic
- Use descriptive mock names: `mock.create_mock("user_repository.save")`
- Verify behavior, not implementation details
- Reset mocks between tests or create fresh instances
- Use `MockRegistry` for tests with many mocks

### Limitations

- No automatic mocking -- you must call `record_call()` manually
- Arguments stored as strings -- ensure consistency
- No trait object support -- use dependency injection to pass mocks

---

## Test Helpers

### Assertion Helpers

```simple
import testing

testing.assert_eq(actual, expected, "message")
testing.assert_ne(actual, unexpected, "message")
testing.assert_true(condition, "message")
testing.assert_false(condition, "message")
val value = testing.assert_some(option, "message")
testing.assert_none(option, "message")
val value = testing.assert_ok(result, "message")
val error = testing.assert_err(result, "message")
```

### Collection Helpers

```simple
testing.assert_contains(list, item, "message")
testing.assert_not_contains(list, item, "message")
testing.assert_empty(list, "message")
testing.assert_len(list, expected_length, "message")
```

### Timing Helpers

```simple
val (result, elapsed_micros) = testing.measure_time(\:
    expensive_operation()
)

val result = testing.assert_fast(
    \: query_database(),
    100000,  # 100ms limit
    "Query should complete in 100ms"
)
```

### Fixture Helpers

```simple
testing.with_cleanup(
    \: create_resource(),      # Setup
    \r: cleanup_resource(r),   # Teardown (runs even on failure)
    \r: test_resource(r)       # Test
)

val result = testing.with_timeout(
    \: potentially_slow_operation(),
    5.0,  # 5 second timeout
    "Operation timed out"
)
```

### Spy Helpers

```simple
val spy = testing.create_spy("function_name")
spy.record_call(["arg1", "arg2"])
testing.assert_called(spy, 3)
testing.assert_called_with(spy, ["arg1", "arg2"])
```

---

## Test Policy and Levels

### Test Levels

| Level | Mock Policy | Coverage Metric | Threshold |
|-------|-------------|-----------------|-----------|
| **Unit** | All mocks allowed | Branch, Condition | 100% |
| **Integration** | HAL-only mocks | Public function touch | 100% |
| **System** | No mocks | Public class/struct touch | 100% |
| **Environment** | HAL/External/Lib mocks | Branch, Condition | 100% |

### Coverage Data Strategy

- **Overall (UT)**: Merges all levels (UT+IT+ST+ENV) for branch/condition metrics
- **IT**: Keeps own raw data for public function coverage
- **ST**: Keeps own raw data for class/struct method coverage

### Running by Level

```bash
simple test --unit          # test/unit/
simple test --integration   # test/integration/
simple test --system        # test/system/
simple test --all           # entire test/
```

### Advanced Test Layers (opt-in)

| Layer | Flag | Purpose |
|-------|------|---------|
| Fuzz | `--fuzz` | Random input crash testing |
| Resilience | `--chaos` | Resource failure recovery |
| Deployment | `--deploy` | Fresh install validation |
| Security | `--security` | Sandbox escape detection |

---

## Test Database

The test database (`doc/test/test_db.sdn` + `test_db_runs.sdn`) provides persistent storage for test execution data, timing statistics, and run history.

### Key Operations

```simple
use app.test_runner_new.test_db_core.TestDatabase

val db = TestDatabase.load().unwrap()

db.update_test_result(
    test_name: "my_test",
    test_file: "test/my_spec.spl",
    suite_name: "My Suite",
    category: "unit",
    status: TestStatus.Passed,
    duration_ms: 42.5
)

db.save()
```

### Safety Mechanisms

- **File locking** with PID-based lock and 10-second timeout
- **Atomic writes** via temp file + rename
- **Automatic backups** before each write
- **Window capping** keeps only 10 most recent timing samples per test

### Recovery

```bash
# Restore from backup
cp doc/test/test_db.sdn.bak doc/test/test_db.sdn

# Clean up stale runs
simple test --cleanup-runs

# Prune old history
simple test --prune-runs=100
```

---

## Platform Organization

Tests are classified by platform compatibility:

| Tier | Tag | Directory | Runs On |
|------|-----|-----------|---------|
| **Shared/Core** | `# @platform: all` | `test/shared/` | Host + Baremetal |
| **Host-only** | *(no tag)* | `test/unit/`, `test/integration/` | Host only |
| **Baremetal-only** | `# @platform: baremetal` | `test/baremetal/` | Baremetal only |

### Shared Test Requirements

A test is shared (`# @platform: all`) when it has zero imports, uses only built-in `describe`/`it`/`expect` matchers, uses only core language features, and does NOT use file I/O, networking, threading, or timers.

### Runtime Skip Helpers

```simple
# @platform: all
describe "Cross-platform math":
    it "basic addition":
        expect(1 + 1).to_equal(2)

    only_on_baremetal "semihost output":
        expect(true).to_equal(true)

    skip_on_baremetal "file write":
        expect(true).to_equal(true)

    only_on_arch "riscv32", "CSR addresses":
        expect(0x300).to_equal(0x300)
```

Available helpers: `skip_on_baremetal`, `only_on_baremetal`, `skip_on_remote`, `only_on_remote`, `only_on_arch`, `skip_on_arch`.

---

## Runner and CLI

### Discovery

Default pattern: `test/**/*_spec.spl`

### Commands

```bash
simple test                        # All tests
simple test path/to/spec.spl      # Specific file
simple test --fail-fast            # Stop on first failure
simple test --seed 12345           # Deterministic order
simple test --format json          # JSON output
simple test --format doc           # Documentation format
simple test --list                 # List tests
simple test --only-slow            # Slow tests only
simple test --screenshots          # Capture GUI screenshots
simple test --refresh-screenshots  # Force recapture
simple test --screenshot-output doc/spec/image/custom
```

### Exit Codes

| Code | Meaning |
|------|---------|
| 0 | All pass |
| 1 | Test failures |
| 2 | Environment failure |
| 3 | Invalid config |

---

## UI System Testing

Shared UI contract testing across the **web backend** and **TUI-web proxy** surfaces. Both backends implement the same HTTP-based test API protocol (Protocol Version 1), allowing a single test suite to verify identical semantic behavior on both surfaces.

**Contract reference:** [`doc/04_architecture/shared_ui_contract.md`](../../04_architecture/shared_ui_contract.md)

**Supported shared surfaces:** web backend (`ui.web`), TUI-web proxy (`ui.tui_web`).
**Not part of shared claim:** native TUI, Electron, Tauri, headless (different transport/protocol).

For screenshot-backed UI verification, the test runner writes captures to `doc/spec/image` by default. Specs can reference those paths through `**Screenshots:**` or `**Artifacts:**` metadata so generated markdown includes links to the captured evidence.

### Architecture

Both the **web backend** (`ui.web`) and the **TUI web proxy** (`ui.tui_web`) expose a shared Test API over HTTP on localhost. Both use the same `handle_test_request` handler from `app.ui.test_api`, ensuring protocol-level parity. The TUI web proxy renders the TUI Screen buffer as terminal-emulator-style HTML (`<pre>` with ANSI colors mapped to CSS spans).

```
System Test (SPipe)
  └─ UITestClient.connect(port)
       └─ HTTP requests ─→ Web Backend (port 8080)
                         ─→ TUI Web Proxy (port 8081)
```

### Starting UI Servers

```bash
# Web backend (test API on localhost by default)
bin/simple ui web app.ui.sdn --port 9001

# TUI over web (headless-friendly terminal emulator view)
bin/simple ui tui_web app.ui.sdn --port 9000

# Allow external access to test API
bin/simple ui web app.ui.sdn --port 9001 --test-api-external
```

### UITestClient

```simple
use std.nogc_sync_mut.ui_test.client.{UITestClient}
use std.nogc_sync_mut.ui_test.types.{ElementInfo, UIStateInfo}

val client = UITestClient.connect("127.0.0.1", 9001)?
client.wait_ready(5000)?

# Actions
client.click("btn_ok")?                          # Click widget
client.type_text("search_input", "query")?       # Type into input
client.submit("form_dialog")?                    # Submit form/dialog
client.drag("item_1", "target")?                  # Drag between widgets
client.send_key("enter")?                         # Send key event
client.focus_next()?                              # Move focus forward
client.focus_prev()?                              # Move focus backward

# Queries
val elem = client.get_element("btn_ok")?          # Widget state + props
val all = client.get_elements()?                   # All widgets
val state = client.get_state()?                    # UI mode, focus, title, element_count
val html = client.screenshot_html()?               # Full HTML snapshot

# Assertions (convenience)
client.check_text("status", "Saved")?             # Check text content
client.check_visible("sidebar")?                   # Check visibility
client.check_focused("search_input")?              # Check focus
client.check_enabled("btn_ok")?                   # Check enabled state
client.check_selected("checkbox_1")?              # Check selection state
client.check_exists("nav_tabs")?                   # Check existence

# Waiting
client.wait_for("modal_dialog", 3000)?             # Wait for element
```

### Test API Endpoints

| Method | Path | Body | Description |
|--------|------|------|-------------|
| POST | `/api/test/click` | `{"id":"X"}` | Inject focus + enter events |
| POST | `/api/test/type` | `{"id":"X","text":"hello"}` | Inject focus + keypress events |
| POST | `/api/test/submit` | `{"id":"X"}` | Submit form/dialog |
| POST | `/api/test/drag` | `{"from_id":"X","to_id":"Y"}` | Synthetic drag events |
| POST | `/api/test/event` | `{"event_type":"key","key":"q"}` | Raw UIEvent injection |
| GET | `/api/test/screenshot` | — | Full HTML render snapshot |
| GET | `/api/test/element?id=X` | — | Element state JSON (id, kind, visible, focused, enabled, selected, text, props) |
| GET | `/api/test/elements` | — | All widgets JSON array |
| GET | `/api/test/state` | — | App state JSON (mode, focused_id, title, theme, element_count, protocol_version) |
| GET | `/api/test/ready` | — | `{"ready":true,"protocol_version":1}` |

**Error model:** All errors return `{"error":"<code>","message":"<text>"}`. Codes: `not_found`, `element_not_found`, `method_not_allowed`, `missing_field`, `unknown_event_type`.

**Protocol version:** All responses include `X-UI-Protocol-Version: 1` header.

### Writing UI System Tests

```simple
# test/system/ui/my_app_spec.spl
# tag: slow, system

use std.nogc_sync_mut.ui_test.client.{UITestClient}

extern fn rt_process_spawn_async(cmd: text, args: [text]) -> i64
extern fn rt_process_kill(pid: i64) -> bool
extern fn rt_thread_sleep(ms: i64)

describe "My App UI":
    it "clicks button and updates status":
        val pid = rt_process_spawn_async("bin/simple",
            ["ui", "web", "test/fixtures/ui/test_app.ui.sdn", "--port", "19042"])
        rt_thread_sleep(1000)

        val client = UITestClient.connect("127.0.0.1", 19042)
        match client:
            Ok(c):
                c.wait_ready(5000)
                c.click("action_btn")
                val focused = c.check_focused("action_btn")
                expect(focused.is_ok()).to_equal(true)
                rt_process_kill(pid)
            Err(e):
                rt_process_kill(pid)
                expect(e).to_equal("")
```

### Test Helpers

Shared helpers in `test/system/ui/helpers/ui_test_helpers.spl`:

```simple
# Start/stop server with cleanup
val pid = start_ui_server("web", "app.ui.sdn", free_port())
# ... run tests ...
stop_ui_server(pid)
```

### Key Files

| File | Purpose |
|------|---------|
| `doc/04_architecture/shared_ui_contract.md` | Shared UI contract (source of truth) |
| `src/app/ui.test_api/handler.spl` | Shared test API request handler |
| `src/app/ui.test_api/json.spl` | JSON serialization for widget state |
| `src/app/ui.web/async_server.spl` | Web backend server |
| `src/app/ui.tui_web/server.spl` | TUI web proxy backend (ANSI→HTML) |
| `src/lib/nogc_sync_mut/ui_test/client.spl` | UITestClient library |
| `src/lib/nogc_sync_mut/ui_test/types.spl` | ElementInfo, UIStateInfo types |
| `src/lib/nogc_sync_mut/ui_test/parse.spl` | JSON response parsing |
| `test/system/ui/helpers/ui_test_helpers.spl` | Server start/stop helpers |
| `test/system/ui/shared_ui_contract_spec.spl` | Cross-surface contract test suite |

### Contract Test Suite

The authoritative cross-surface proof suite is `test/system/ui/shared_ui_contract_spec.spl`. It starts BOTH web and tui_web backends against the same fixture and verifies identical behavior across 7 categories:

1. **Protocol** — ready endpoint, protocol version, structured errors
2. **Tree/Read** — elements, element IDs, kind consistency, screenshots
3. **Actions** — click, type, submit, drag, send_key
4. **Focus/State** — focus_next, focus_prev, visibility, enabled
5. **State Endpoint** — element_count, protocol_version
6. **Errors** — element_not_found, missing_field, unknown_event_type
7. **Consistency** — read-after-write after click

Run with:
```bash
bin/simple test test/system/ui/shared_ui_contract_spec.spl --tag slow
```

### Security

- Test API binds to `127.0.0.1` (localhost) by default on both backends
- Use `--test-api-external` flag to bind to `0.0.0.0` for remote access
- No authentication — intended for local/CI testing only

---

## Best Practices

### Do

- One assertion concept per test
- Use descriptive test names: `it "returns error when user not found"`
- Use `context` for related test groups
- Use `given_lazy` for test data
- Tag appropriately (`@slow`, `@integration`)
- Clean up with `after_each` or `with_cleanup`
- Provide meaningful error messages in assertions
- Use helpers: `testing.assert_some(result, "message")` instead of manual unwrapping

### Don't

- Multiple unrelated behaviors per test
- Test implementation details
- Share mutable state between tests
- Use vague test names like `it "works"`
- Skip tests without marking `pending`
- Over-verify mocks -- verify behavior, not call counts

### Interpreter Mode Limitation

The interpreter mode test runner only verifies file loading. The `it` block bodies do not execute in interpreter mode. Use compiled mode for actual execution of test logic.

---

## Troubleshooting

### Fixture not available

```simple
# Wrong -- fixture not defined:
it "uses user":
    expect user.name == "Alice"

# Right -- define fixture first:
given_lazy :user, \:
    { name: "Alice" }
it "uses user":
    expect user.name == "Alice"
```

### State leaking between tests

Use `given:` blocks to reset state before each test instead of `let` at context level.

### Mock not recording calls

1. Ensure you call `mock.record_call()` in your code
2. Check mock reference (same instance)
3. Print `mock.summary()` to inspect call history

### Wrong mock arguments

Arguments are stored as strings. Ensure consistency:

```simple
mock.record_call(["123", "Alice"])       # Use strings
mock.was_called_with(["123", "Alice"])   # Match strings
```

### Tests are slow

1. Reduce dataset sizes (10x reduction yields ~10x speedup)
2. Mock expensive operations (I/O, network)
3. Tag slow tests with `slow_it` and run separately
4. Split large test files into logical categories

### Benchmarks show high variance

1. Increase sample size and warmup iterations
2. Run on idle machine
3. Use median instead of mean for skewed distributions
