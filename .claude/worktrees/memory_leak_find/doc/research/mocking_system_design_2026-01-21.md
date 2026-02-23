# Mocking System Design for Simple Language

**Date:** 2026-01-21
**Status:** Research Complete
**Author:** Claude Code

---

## Executive Summary

This document presents research and design for a simple, easy-to-use mocking system for the Simple language. It covers:

1. **Existing infrastructure analysis** - What we already have
2. **Best practices research** - Industry patterns and frameworks
3. **Mock prevention mechanisms** - Ensuring mocks don't leak into system tests
4. **Proposed design** - A Simple-native mocking system

---

## 1. Current State Analysis

### 1.1 What Exists

| Component | Status | Location |
|-----------|--------|----------|
| Mock API Spec | Designed | `doc/spec/testing/mock.md` |
| Rust Fluent API | Implemented | `src/rust/util/simple_mock_helper/` |
| Mock Policy System | Implemented | `simple_mock_helper::mock_policy` |
| SSpec Framework | Production-ready | `src/lib/std/src/spec/` |
| Mock Types (Simple) | NOT implemented | Placeholder only |

### 1.2 Existing Rust Mock Helper Features

The Rust-side `simple_mock_helper` crate provides:

**Fluent API:**
```rust
// Setup
setup.when("findById").with_args(&[123]).returns("User").times(1);

// Verification
verify.method("findById").was_called().with_args(&[123]).once();

// Deep call chains
setup.when("getLibrary").chain("getHead").chain("getName").returns("Jane");
```

**Argument Matchers:**
- `Any` - Match any value
- `Exact(value)` - Match exact value
- `GreaterThan(n)`, `LessThan(n)` - Numeric comparisons
- `Range(min, max)` - Range matching
- `Pattern(regex)` - Regex matching
- `Predicate(desc)` - Custom predicates

**Mock Policy (key for preventing mock leaks):**
```rust
// Unit tests - allow all mocks
init_mocks_for_only(&["*"]);

// Integration tests - HAL-only mocks
init_mocks_for_only_default();  // *::hal::*, *::sub_hal::*

// System tests - NO mocks
init_mocks_for_system();

// Each mock call checks policy
check_mock_use_from(module_path!());
```

---

## 2. Industry Research: Mocking Best Practices

### 2.1 Test Double Terminology

| Type | Purpose | Verification |
|------|---------|--------------|
| **Stub** | Canned responses, no verification | State |
| **Mock** | Behavior verification | Behavioral |
| **Spy** | Records calls for later verification | Behavioral |
| **Fake** | Lightweight implementation | State |

**2026 Perspective:** The distinction has blurred in practice. Modern frameworks unify these under "test double" with configurable behavior.

### 2.2 Key Design Patterns

**Pattern 1: Dependency Injection**
- Mocks must be injectable at construction
- Constructor injection preferred over property/field injection
- Interface-based mocking enables easy substitution

**Pattern 2: Nullables (James Shore)**
- Objects that can operate in "null" mode without external systems
- No mocks needed for many tests
- Avoids mock complexity in simple cases

**Pattern 3: Functional Core, Imperative Shell**
- Pure business logic (no mocks needed)
- Thin shell for I/O (mocks concentrated here)
- Reduces overall mock usage

**Pattern 4: In-Memory Fakes**
- Lightweight real implementations for testing
- More realistic than mocks
- Requires maintenance but catches integration bugs

### 2.3 When to Avoid Mocks

From [Testing Without Mocks](http://www.jamesshore.com/v2/projects/nullables/testing-without-mocks):

| Test Type | Mock Strategy |
|-----------|---------------|
| Unit | Mocks OK for isolation |
| Integration | Prefer fakes or real implementations |
| System/E2E | NO mocks - test real system |

**Why avoid mocks in integration/system tests:**
1. False confidence - mocks behave as configured, not as real system
2. Tight coupling - mock config tied to implementation
3. Fragile tests - refactoring breaks mock configurations
4. Hidden bugs - mismatched mock/real behavior

---

## 3. Mock Prevention Mechanisms

### 3.1 Policy-Based Approach (Recommended)

**Design:** Runtime policy check on every mock instantiation/call.

```simple
# At test binary initialization
@system_test
fn main():
    MockPolicy.set_mode(MockMode.DISABLED)  # No mocks allowed
    run_tests()

# In mock implementation
struct Mock<T>:
    fn new() -> Mock<T>:
        MockPolicy.check_allowed()  # Panics if disabled
        # ... create mock
```

**Policies:**
| Mode | Allowed Modules | Use Case |
|------|-----------------|----------|
| `ALL` | `*` | Unit tests |
| `HAL_ONLY` | `*::hal::*`, `*::sub_hal::*` | Integration |
| `DISABLED` | None | System tests |
| `CUSTOM(patterns)` | User-specified | Fine-grained control |

### 3.2 Compile-Time Approach

**Design:** Feature flags to exclude mock code entirely.

```toml
# Cargo.toml equivalent
[features]
mock = []        # Include mock types
unit-test = ["mock"]
integration-test = []  # No mock feature
system-test = []       # No mock feature
```

```simple
# In mock module
#[cfg(feature = "mock")]
struct Mock<T>:
    ...

# Won't compile if mock feature not enabled
```

**Pros:** Zero runtime overhead, impossible to accidentally use mocks
**Cons:** Requires separate build configurations

### 3.3 Test Tag Approach

**Design:** Use test tags to enforce mock restrictions.

```simple
@tag("system")
@no_mocks  # Decorator that fails if mocks are used
describe "Full System Test":
    it "processes end-to-end":
        # Mock usage here would fail the test
        ...
```

**Implementation:**
- `@no_mocks` decorator wraps test in mock-checking context
- Any mock instantiation during test execution causes immediate failure
- Clear error message: "Mock 'X' used in system test 'Y'"

### 3.4 Test Directory Convention

**Design:** Convention-based, directory determines mock availability.

```
test/
├── unit/           # Mocks available
├── integration/    # Limited mocks (HAL only)
└── system/         # No mocks
```

**Implementation:**
- Test runner detects test category from path
- Automatically sets mock policy based on directory
- No manual configuration needed

### 3.5 Recommended: Layered Approach

Combine multiple mechanisms:

1. **Runtime policy** (primary) - Catches violations at runtime
2. **Test tags** (explicit) - Documents intent
3. **Directory convention** (implicit) - Default behavior

```simple
# test/system/checkout_flow_spec.spl
@tag("system")
describe "Checkout Flow":
    # MockPolicy automatically DISABLED because in system/ directory
    # @no_mocks decorator available for explicit marking

    it "completes purchase with real payment provider":
        # Any mock usage panics with clear error
        ...
```

---

## 4. Proposed Simple Language Mock Design

### 4.1 Core Types

```simple
# Test doubles
mock Double<T>     # Mock implementing interface T
spy Spy<T>         # Spy recording calls
stub Stub<T>       # Simple stub with canned responses

# Argument matchers
enum ArgMatcher:
    Any
    Exact(value: Any)
    Gt(n: Number)
    Lt(n: Number)
    Range(min: Number, max: Number)
    Pattern(regex: String)
    Custom(predicate: fn(Any) -> Bool)

# Verification counts
enum Times:
    Once
    Exactly(n: Int)
    AtLeast(n: Int)
    AtMost(n: Int)
    Never
    AnyTimes
```

### 4.2 Creation Syntax

```simple
# Create mock implementing interface
val user_dao = mock UserDao

# Create spy wrapping real object
val service_spy = spy MyService.new()

# Create simple stub
val config_stub = stub Config:
    get("timeout"): 30
    get("retries"): 3
```

### 4.3 Stubbing Behavior

```simple
# Basic stubbing
user_dao.when(:find_by_id).with(123).returns(User(id: 123, name: "Alice"))

# Sequential returns
counter.when(:next).returns_once(1).returns_once(2).returns(3)

# Throws exception
api.when(:call).raises(NetworkError("timeout"))

# Deep call chains
library.when(:get_librarian).chain(:get_name).returns("Jane")

# Argument matchers
dao.when(:save).with(any(User), gt(0)).returns(true)
```

### 4.4 Verification

```simple
# Basic verification
notifier.verify(:notify).called()

# Call count
service.verify(:process).called_times(3)

# Arguments
dao.verify(:save).called_with(User(id: 1))

# Fluent chaining
api.verify(:call)
   .was_called()
   .with_args("GET", "/users")
   .times(Times.AtLeast(1))
```

### 4.5 Integration with SSpec

```simple
describe "UserService":
    given :repo: mock UserRepository
    given :notifier: mock Notifier

    before_each:
        get_let(:repo).reset()
        get_let(:notifier).reset()

    context "creating a user":
        before_each:
            get_let(:repo).when(:save).with(any(User)).returns(User(id: 1))
            get_let(:notifier).when(:notify).returns(())

        it "saves to repository":
            service = UserService(get_let(:repo), get_let(:notifier))
            service.create_user("Alice")

            get_let(:repo).verify(:save).called()

        it "sends notification":
            service = UserService(get_let(:repo), get_let(:notifier))
            service.create_user("Alice")

            get_let(:notifier).verify(:notify).called_with("user_created", 1)
```

### 4.6 Mock Policy Integration

```simple
# In test/unit/__init__.spl
MockPolicy.init(MockMode.ALL)

# In test/integration/__init__.spl
MockPolicy.init(MockMode.HAL_ONLY)

# In test/system/__init__.spl
MockPolicy.init(MockMode.DISABLED)

# Manual override (rare)
@allow_mocks(["*::cache::*"])
describe "Cache Integration":
    # Only cache mocks allowed
    ...
```

### 4.7 Auto-Reset Between Tests

```simple
# Automatic in SSpec - mocks reset after each test
describe "Service":
    given :mock: mock Dependency

    it "first test":
        # mock is fresh
        ...

    it "second test":
        # mock is fresh again, previous stubbing/verification cleared
        ...
```

---

## 5. Implementation Roadmap

### Phase 1: Foundation (Core Types)
- [ ] `Mock<T>` core type with method interception
- [ ] `when()` stubbing method
- [ ] `returns()` and `raises()` behaviors
- [ ] Mock policy runtime checks
- [ ] Basic integration with SSpec `given`

### Phase 2: Verification
- [ ] `verify()` method
- [ ] Call recording
- [ ] `called()`, `called_times()`, `called_with()`
- [ ] Verification failure messages

### Phase 3: Matchers
- [ ] `any()`, `gt()`, `lt()` argument matchers
- [ ] Pattern matching for arguments
- [ ] Custom predicate matchers
- [ ] Integration with existing `expect` matchers

### Phase 4: Advanced Features
- [ ] Deep call chains (`.chain()`)
- [ ] Sequential returns (`.returns_once()`)
- [ ] Spy wrapping real objects
- [ ] Async mock support

### Phase 5: Polish
- [ ] Auto-reset between tests
- [ ] Clear error messages
- [ ] Documentation and examples
- [ ] Performance optimization

---

## 6. Alternative Approaches Considered

### 6.1 Manual Fake Objects

**Approach:** Users write their own fake implementations.

```simple
struct FakeUserRepository(users: Dict<Int, User>):
    fn find_by_id(id: Int) -> Option<User>:
        users.get(id)

    fn save(user: User) -> User:
        users.insert(user.id, user)
        user
```

**Pros:**
- No framework needed
- Full control
- No mock leak issues

**Cons:**
- Boilerplate for every interface
- No verification of interactions
- Easy to get out of sync

**Verdict:** Good for stable interfaces, supplement with mocks for complex scenarios.

### 6.2 Record/Replay

**Approach:** Record real interactions, replay in tests.

```simple
# Record mode
val recorder = MockRecorder.new()
recorder.start_recording()
# ... run real code ...
recorder.save("user_service_interactions.json")

# Replay mode
val mock = Mock.from_recording("user_service_interactions.json")
```

**Pros:**
- Realistic behavior
- No manual stubbing
- Catches real API changes

**Cons:**
- Requires real system for recording
- Large recording files
- Brittleness with changing data

**Verdict:** Consider for Phase 6 as optional feature.

### 6.3 Contract Testing

**Approach:** Define contracts, verify both mock and real implementation.

```simple
contract UserRepositoryContract:
    it "finds existing user":
        repo.save(User(id: 1, name: "Test"))
        result = repo.find_by_id(1)
        expect(result).to(be_some())

    it "returns None for missing user":
        result = repo.find_by_id(999)
        expect(result).to(be_none())

# Apply contract to mock
describe "MockUserRepository":
    include_contract(UserRepositoryContract, mock UserRepository)

# Apply contract to real implementation
describe "SqlUserRepository":
    include_contract(UserRepositoryContract, SqlUserRepository.new(test_db))
```

**Verdict:** Consider for Phase 6, ensures mock/real parity.

---

## 7. Comparison with Other Frameworks

| Feature | Simple (Proposed) | RSpec Mocks | Mockito | Jest |
|---------|-------------------|-------------|---------|------|
| Type safety | Compile-time | Runtime | Compile-time | Runtime |
| Fluent API | Yes | Yes | Yes | Yes |
| Spies | Yes | Yes | Yes | Yes |
| Deep chains | Yes | Partial | Yes | Yes |
| Arg matchers | Yes | Yes | Yes | Yes |
| Auto-reset | Yes | Yes | Manual | Yes |
| Mock policy | **Yes** | No | No | No |
| Verification | Behavioral | Behavioral | Behavioral | Behavioral |

**Unique to Simple:** Built-in mock policy system prevents accidental mock usage in system tests.

---

## 8. Summary

### Key Design Decisions

1. **Unified mock type** - Single `Mock<T>` type covers mock/stub use cases
2. **Separate `Spy<T>`** - For recording calls to real objects
3. **Fluent API** - `when().with().returns()` pattern
4. **Policy-based prevention** - Runtime checks prevent mock leaks
5. **SSpec integration** - Works with existing `given`/`let` fixture system
6. **Auto-reset** - Mocks automatically reset between tests

### Mock Prevention Strategy

**Primary:** Runtime mock policy with three modes:
- `ALL` - Unit tests
- `HAL_ONLY` - Integration tests
- `DISABLED` - System tests

**Secondary:** Test directory convention sets default policy.

**Tertiary:** `@no_mocks` tag for explicit documentation.

### Next Steps

1. Review this design with team
2. Implement Phase 1 (Foundation)
3. Write comprehensive test suite
4. Document in SSpec guide

---

## References

- [Testing Without Mocks - James Shore](http://www.jamesshore.com/v2/projects/nullables/testing-without-mocks)
- [Mock Object Pattern - PMI](https://www.pmi.org/disciplined-agile/the-design-patterns-repository/the-mock-object-pattern)
- [Mocking in Unit Tests - Microsoft](https://microsoft.github.io/code-with-engineering-playbook/automated-testing/unit-testing/mocking/)
- [Test Isolation Is About Avoiding Mocks](https://www.destroyallsoftware.com/blog/2014/test-isolation-is-about-avoiding-mocks)
- [Focus on Integration Tests Instead of Mock-Based Tests](https://phauer.com/2019/focus-integration-tests-mock-based-tests/)
- [We Need to Stop Calling Everything a Mock - 2026](https://coding-is-like-cooking.info/2026/01/we-need-to-stop-calling-everything-a-mock/)
- Existing: `doc/spec/testing/mock.md`
- Existing: `src/rust/util/simple_mock_helper/`
