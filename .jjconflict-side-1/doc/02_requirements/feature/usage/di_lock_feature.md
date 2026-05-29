# di lock feature
*Source:* `test/feature/usage/di_lock_feature_spec.spl`

## Feature: DI Lock Feature: Phase 1 - Lock state

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | starts unlocked | pass |
| 2 | lock() transitions to locked state | pass |
| 3 | is_locked() returns true after lock | pass |
| 4 | unlock() transitions back to unlocked | pass |
| 5 | is_locked() returns false after unlock | pass |
| 6 | is_locked() returns false on fresh container | pass |

**Example:** starts unlocked
    Given val di = make_di()
    Then  expect(di.locked).to_equal(false)

**Example:** lock() transitions to locked state
    Given val di = make_di()
    Then  expect(di.locked).to_equal(true)

**Example:** is_locked() returns true after lock
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(true)

**Example:** unlock() transitions back to unlocked
    Given val di = make_di()
    Then  expect(di.locked).to_equal(false)

**Example:** is_locked() returns false after unlock
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(false)

**Example:** is_locked() returns false on fresh container
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(false)

## Feature: DI Lock Feature: Phase 2 - Locked behavior

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | locked container rejects bind_instance | pass |
| 2 | locked container rejects bind | pass |
| 3 | locked container still allows resolve | pass |
| 4 | locked container still allows resolve_or | pass |
| 5 | locked container still allows has check | pass |
| 6 | locked container resolve_or returns default for missing | pass |
| 7 | locked container rejects bind_tagged | pass |

**Example:** locked container rejects bind_instance
    Given val di = make_di()
    Then  expect(di.has("Bar")).to_equal(false)

**Example:** locked container rejects bind
    Given val di = make_di()
    Then  expect(di.has("Baz")).to_equal(false)

**Example:** locked container still allows resolve
    Given val di = make_di()
    Given val result = di.resolve("Svc")
    Then  expect(result).to_equal("hello")

**Example:** locked container still allows resolve_or
    Given val di = make_di()
    Given val result = di.resolve_or("Svc", "default")
    Then  expect(result).to_equal("hello")

**Example:** locked container still allows has check
    Given val di = make_di()
    Then  expect(di.has("Svc")).to_equal(true)

**Example:** locked container resolve_or returns default for missing
    Given val di = make_di()
    Given val result = di.resolve_or("Missing", "fallback")
    Then  expect(result).to_equal("fallback")

**Example:** locked container rejects bind_tagged
    Given val di = make_di()
    Then  expect(di.has("Tagged")).to_equal(false)

## Feature: DI Lock Feature: Phase 3 - Lock semantics

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | can lock and unlock multiple times | pass |
| 2 | bindings before lock are preserved after lock | pass |
| 3 | unlock allows new bindings again | pass |
| 4 | pre-lock binding not overwritten when locked | pass |
| 5 | locked state does not affect resolve_or nil default | pass |

**Example:** can lock and unlock multiple times
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(true)
    Then  expect(di.is_locked()).to_equal(false)
    Then  expect(di.is_locked()).to_equal(true)
    Then  expect(di.is_locked()).to_equal(false)

**Example:** bindings before lock are preserved after lock
    Given val di = make_di()
    Then  expect(di.resolve("Backend")).to_equal("production-backend")
    Then  expect(di.resolve("Logger")).to_equal("file-logger")

**Example:** unlock allows new bindings again
    Given val di = make_di()
    Then  expect(di.has("Foo")).to_equal(false)
    Then  expect(di.has("Foo")).to_equal(true)

**Example:** pre-lock binding not overwritten when locked
    Given val di = make_di()
    Given val result = di.resolve("Backend")
    Then  expect(result).to_equal("production-backend")

**Example:** locked state does not affect resolve_or nil default
    Given val di = make_di()
    Given val result = di.resolve_or("NoSuch", nil)
    Then  expect(result).to_be_nil()

## Feature: DI Lock Feature: Phase 4 - Integration

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | container locked after setup phase | pass |
| 2 | runtime resolution works on locked container | pass |
| 3 | locked container with resolve_singleton works | pass |
| 4 | multiple services still resolvable after lock | pass |
| 5 | env-var lock blocks bind_instance | pass |
| 6 | env-var di_test bypass allows bind_instance | pass |

**Example:** container locked after setup phase
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(true)

**Example:** runtime resolution works on locked container
    Given val di = make_di()
    Given val result = di.resolve("Config")
    Then  expect(result).to_equal("prod-config")

**Example:** locked container with resolve_singleton works
    Given val di = make_di()
    Given val result = di.resolve("Singleton")
    Then  expect(result).to_equal("singleton-value")

**Example:** multiple services still resolvable after lock
    Given val di = make_di()
    Then  expect(di.resolve("A")).to_equal("alpha")
    Then  expect(di.resolve("B")).to_equal("beta")
    Then  expect(di.resolve("C")).to_equal("gamma")

**Example:** env-var lock blocks bind_instance
    Given val di = make_di()
    Then  expect(di.has("MockService")).to_equal(false)

**Example:** env-var di_test bypass allows bind_instance
    Given val di = make_di()
    Then  expect(di.has("TestMock")).to_equal(true)

## Feature: DI Lock Feature: Phase 5 - System test

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | full registration-lock-resolve cycle works | pass |
| 2 | complete lifecycle: register, lock, reject, unlock, register again | pass |
| 3 | factory bindings registered before lock resolve correctly | pass |
| 4 | di_is_system_test_locked returns false with no env vars | pass |
| 5 | di_is_system_test_locked returns true with SIMPLE_SYSTEM_TEST=1 | pass |

**Example:** full registration-lock-resolve cycle works
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(true)
    Then  expect(di.resolve("key1")).to_equal("val1")
    Then  expect(di.resolve("key2")).to_equal("val2")

**Example:** complete lifecycle: register, lock, reject, unlock, register again
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(true)
    Then  expect(di.has("Extra")).to_equal(false)
    Then  expect(di.resolve("Core")).to_equal("core-impl")
    Then  expect(di.has("Extra")).to_equal(true)

**Example:** factory bindings registered before lock resolve correctly
    Given val di = make_di()
    Given val result = di.resolve("LazyService")
    Then  expect(result).to_equal("created-on-demand")

**Example:** di_is_system_test_locked returns false with no env vars
    Given val locked = di_is_system_test_locked()
    Then  expect(locked).to_equal(false)

**Example:** di_is_system_test_locked returns true with SIMPLE_SYSTEM_TEST=1
    Given val locked = di_is_system_test_locked()
    Then  expect(locked).to_equal(true)


