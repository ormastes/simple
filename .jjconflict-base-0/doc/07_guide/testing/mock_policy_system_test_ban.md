# Mock Policy: System Test Mock Ban

**Status:** Implemented
**Category:** Testing / Mock Prevention
**Related:** `src/compiler_rust/lib/std/src/spec/mock.spl`, `src/compiler_rust/lib/std/src/spec/registry.spl`

---

## Overview

The Simple language enforces mock prevention at the language level through a **mock policy system**. This prevents test doubles (mocks, spies, stubs) from leaking into system and integration tests, where they can mask real failures.

The policy is enforced on every `Mock.new()`, `Spy.new()`, and `Stub.new()` call. When the policy disallows mocks, these constructors panic with a clear diagnostic message.

---

## Mock Modes

| Mode | Enum Value | Use Case | Behavior |
|------|-----------|----------|----------|
| **All** | `MockMode.All` | Unit tests | All mocks allowed (default) |
| **HAL-Only** | `MockMode.HalOnly` | Integration tests | Only `.hal.` and `.sub_hal.` modules may mock |
| **Disabled** | `MockMode.Disabled` | System tests | **No mocks at all** — panics on creation |
| **Custom** | `MockMode.Custom` | Specialized | Pattern-based `*` wildcard restriction |

---

## Quick Start

### Unit Tests (default — mocks allowed)

```simple
use std.spec.*

describe "UserService":
    it "returns cached user":
        val cache = mock("cache")
        cache.when("get").returns(User(name: "Alice"))
        # Works fine — MockMode.All is the default
```

### System Tests (mock ban active)

```simple
use std.spec.*
use std.spec.mock.{mock_policy_disable, mock_policy_reset}

describe "UserService System Test":
    before_each:
        mock_policy_disable()   # Enable system test mode

    after_each:
        mock_policy_reset()     # Restore default

    it "uses real database":
        # Real dependencies — no mocks needed
        val user = UserService.find(1)
        expect(user.name).to_equal("Alice")

    it "cannot create mocks":
        # This would PANIC:
        # val cache = mock("cache")
        # Error: "Mock used while mocks are disabled (system test policy)"
        pass_do_nothing
```

### Integration Tests (HAL-only mocks)

```simple
use std.spec.mock.{mock_policy_init_hal_only, mock_policy_reset}

describe "SPI Driver Integration":
    before_each:
        mock_policy_init_hal_only()

    after_each:
        mock_policy_reset()

    it "allows HAL mock":
        # Allowed — source contains .hal.
        val spi = mock("driver.hal.spi")
        spi.when("transfer").returns([0x00, 0xFF])

    it "blocks service mock":
        # PANICS: "Mock from 'app.service' not allowed.
        #          Only HAL mocks permitted in integration tests."
        # val svc = mock("app.service")
        pass_do_nothing
```

---

## Setting Mock Mode on Test Groups

Mock mode can be set at the `ExampleGroup` (describe/context) level, and it **inherits downward** through the group hierarchy.

### Per-Group (compiled mode with SSpec executor)

```simple
use std.spec.{describe, it, expect}
use std.spec.registry.{MockMode}

# The executor reads the group's mock_mode and enforces it
# before running each test example.
#
# Group-level mock_mode propagates to all child examples
# unless an example explicitly overrides it.
```

### Programmatic API

```simple
use std.spec.mock.{MockPolicy, MockMode}

# Initialize for current test binary
MockPolicy.init(MockMode.Disabled)

# Or use convenience functions
MockPolicy.disable()           # System test mode
MockPolicy.init_hal_only()     # Integration mode
MockPolicy.reset()             # Back to All

# Query current state
MockPolicy.is_enabled()        # false when Disabled
MockPolicy.current_mode()      # MockMode.Disabled

# Check a specific module path
MockPolicy.check_allowed("app.service.user")  # panics if not allowed
```

---

## Architecture

### Enforcement Layers

```
                 Simple Code
                     |
    mock("name") / spy("name") / stub("name")
                     |
         Mock.new() / Spy.new() / Stub.new()
                     |
        mock_policy_check_disabled()        <-- Simple-side gate (Disabled only)
                     |
              (test executes)
                     |
    Executor sets both layers before each test:
      mock_policy_disable()                 <-- Simple-side state
      __mock_policy_disable()               <-- Rust-side state (FFI)
                     |
    Rust FFI: check_mock_use_from(          <-- Rust-side pattern gate
      module_path!()                            (uses real caller module path)
    )
```

**Two enforcement layers with distinct roles:**

1. **Simple-side constructor gate** (`mock_policy_check_disabled()`): Called inside `Mock.new()` / `Spy.new()` / `Stub.new()`. Only checks `Disabled` mode — panics if mocks are completely banned. Takes **no arguments**, so it can't be spoofed by naming a mock `"my.hal.fake"`. HalOnly/Custom pattern checks are NOT done here because constructors don't have access to the caller's module path.

2. **Rust-side pattern gate** (`check_mock_use_from(module_path!())`): Called via FFI by the executor and compiled-mode runtime. Uses the **real caller module path** (compile-time `module_path!()` macro), so HalOnly/Custom patterns can't be spoofed. Enforces all four modes.

The SSpec executor (`spec/runner/executor.spl`) synchronizes **both** layers before each test by calling both the Simple-side functions (`mock_policy_disable()`) and the Rust FFI functions (`__mock_policy_disable()`).

### Group Inheritance

```
describe "System Tests"              mock_mode: Disabled
    context "API endpoints"          inherits: Disabled
        it "health check"            effective: Disabled (from group)
        it "special case"            effective: HalOnly  (explicit override)
    context "Database"               inherits: Disabled
        it "migration"               effective: Disabled (from group)
```

`ExampleGroup.get_effective_mock_mode()` walks up the parent chain until it finds a group with an explicit `mock_mode`, defaulting to `MockMode.All`.

**Explicit overrides:** `Example.mock_mode` is `Option<MockMode>` — `nil` means "inherit from group", `Some(mode)` means "use this mode regardless of group". This means `.unit_test()` / `.with_mock_mode(MockMode.All)` on an example inside a `Disabled` group correctly overrides the ban for that specific test.

---

## Error Messages

| Scenario | Message |
|----------|---------|
| Disabled mode | `Mock used while mocks are disabled (system test policy). Source: <module>` |
| HalOnly + non-HAL | `Mock from '<module>' not allowed. Only HAL mocks permitted in integration tests.` |
| Custom + no match | `Mock from '<module>' not allowed by current mock policy.` |

---

## Custom Pattern Syntax

Patterns use `*` as a wildcard matching any character sequence.

| Pattern | Matches | Doesn't Match |
|---------|---------|---------------|
| `*` | Everything | — |
| `*.hal.*` | `driver.hal.spi` | `app.service` |
| `cache` | `app.cache.redis` | `app.service` |
| `*.hal.*`, `*.io.*` | `driver.hal.spi`, `net.io.tcp` | `app.db` |

```simple
use std.spec.mock.{mock_policy_init_with_patterns, mock_policy_reset}

mock_policy_init_with_patterns(["*.hal.*", "*.io.*", "*.driver.*"])
# Now only modules matching these patterns can create mocks
```

---

## Test Levels Summary

| Test Level | Mock Mode | Rationale |
|------------|-----------|-----------|
| Unit | `All` | Test in isolation, mock all dependencies |
| Integration | `HalOnly` | Real services, mock only hardware abstraction |
| System | `Disabled` | Full stack, no fakes — catches integration bugs |
| Environment | `Custom` | Mock external dependencies (HAL + libs + IO) |

---

## Files

| File | Purpose |
|------|---------|
| `src/compiler_rust/lib/std/src/spec/mock.spl` | Mock policy + Mock/Spy/Stub classes |
| `src/compiler_rust/lib/std/src/spec/registry.spl` | MockMode enum, Example/ExampleGroup types |
| `src/compiler_rust/lib/std/src/spec/runner/executor.spl` | Per-test policy initialization |
| `src/compiler_rust/compiler/src/mock_helper/mock_policy.rs` | Rust-side atomic policy enforcement |
| `src/compiler_rust/compiler/src/interpreter_extern/mock_policy.rs` | FFI bridges for Simple code |
| `test/unit/lib/nogc_sync_mut/mock_policy_spec.spl` | SSpec tests for mock ban |
