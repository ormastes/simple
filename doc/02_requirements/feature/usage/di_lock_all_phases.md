# di lock all phases
*Source:* `test/feature/usage/di_lock_all_phases_spec.spl`

## Feature: DI Lock: Phase 1 - Lock state transitions

### Scenario: initial state

| # | Example | Status |
|---|---------|--------|
| 1 | new container is unlocked | pass |
| 2 | locked field is false on construction | pass |
| 3 | binding works before any lock | pass |

**Example:** new container is unlocked
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(false)

**Example:** locked field is false on construction
    Given val di = make_di()
    Then  expect(di.locked).to_equal(false)

**Example:** binding works before any lock
    Given val di = make_di()
    Then  expect(di.has("Svc")).to_equal(true)

### Scenario: lock transitions

| # | Example | Status |
|---|---------|--------|
| 1 | lock sets is_locked to true | pass |
| 2 | unlock after lock sets is_locked to false | pass |
| 3 | multiple lock calls remain locked | pass |
| 4 | unlock without prior lock stays unlocked | pass |
| 5 | lock-unlock-lock cycle ends locked | pass |

**Example:** lock sets is_locked to true
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(true)

**Example:** unlock after lock sets is_locked to false
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(false)

**Example:** multiple lock calls remain locked
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(true)

**Example:** unlock without prior lock stays unlocked
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(false)

**Example:** lock-unlock-lock cycle ends locked
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(true)

## Feature: DI Lock: Phase 2 - Binding behavior when locked

### Scenario: bind_instance is blocked

| # | Example | Status |
|---|---------|--------|
| 1 | bind_instance rejected when locked | pass |
| 2 | bind_instance succeeds before lock | pass |

**Example:** bind_instance rejected when locked
    Given val di = make_di()
    Then  expect(di.has("Blocked")).to_equal(false)

**Example:** bind_instance succeeds before lock
    Given val di = make_di()
    Then  expect(di.has("PreLock")).to_equal(true)

### Scenario: bind factory is blocked

| # | Example | Status |
|---|---------|--------|
| 1 | bind factory rejected when locked | pass |
| 2 | bind_tagged rejected when locked | pass |

**Example:** bind factory rejected when locked
    Given val di = make_di()
    Then  expect(di.has("FactoryBlocked")).to_equal(false)

**Example:** bind_tagged rejected when locked
    Given val di = make_di()
    Then  expect(di.has("TaggedBlocked")).to_equal(false)

### Scenario: bind allowed after unlock

| # | Example | Status |
|---|---------|--------|
| 1 | bind_instance works after unlock | pass |
| 2 | bind factory works after unlock | pass |

**Example:** bind_instance works after unlock
    Given val di = make_di()
    Then  expect(di.has("Blocked")).to_equal(false)
    Then  expect(di.has("Allowed")).to_equal(true)

**Example:** bind factory works after unlock
    Given val di = make_di()
    Then  expect(di.has("FactoryAfterUnlock")).to_equal(true)

## Feature: DI Lock: Phase 3 - Resolution behavior

### Scenario: resolve works while locked

| # | Example | Status |
|---|---------|--------|
| 1 | resolve pre-lock singleton works | pass |
| 2 | resolve pre-lock factory works | pass |

**Example:** resolve pre-lock singleton works
    Given val di = make_di()
    Then  expect(di.resolve("Config")).to_equal("prod-config")

**Example:** resolve pre-lock factory works
    Given val di = make_di()
    Then  expect(di.resolve("Builder")).to_equal("built-value")

### Scenario: resolve_or works while locked

| # | Example | Status |
|---|---------|--------|
| 1 | resolve_or returns registered value when locked | pass |
| 2 | resolve_or returns default for missing when locked | pass |

**Example:** resolve_or returns registered value when locked
    Given val di = make_di()
    Then  expect(di.resolve_or("Setting", "off")).to_equal("on")

**Example:** resolve_or returns default for missing when locked
    Given val di = make_di()
    Then  expect(di.resolve_or("Missing", "fallback")).to_equal("fallback")

### Scenario: has works correctly

| # | Example | Status |
|---|---------|--------|
| 1 | has returns true for pre-lock binding | pass |
| 2 | has returns false for post-lock rejected binding | pass |

**Example:** has returns true for pre-lock binding
    Given val di = make_di()
    Then  expect(di.has("Present")).to_equal(true)

**Example:** has returns false for post-lock rejected binding
    Given val di = make_di()
    Then  expect(di.has("Rejected")).to_equal(false)

## Feature: DI Lock: Phase 4 - Lock integration with registration

### Scenario: protects production bindings

| # | Example | Status |
|---|---------|--------|
| 1 | pre-lock binding cannot be overwritten while locked | pass |
| 2 | multiple pre-lock bindings all resolvable after lock | pass |

**Example:** pre-lock binding cannot be overwritten while locked
    Given val di = make_di()
    Then  expect(di.resolve("Backend")).to_equal("production-backend")

**Example:** multiple pre-lock bindings all resolvable after lock
    Given val di = make_di()
    Then  expect(di.resolve("Backend")).to_equal("production-backend")
    Then  expect(di.resolve("Logger")).to_equal("file-logger")
    Then  expect(di.resolve("Config")).to_equal("prod-config")

### Scenario: extend after unlock

| # | Example | Status |
|---|---------|--------|
| 1 | new bindings added after unlock are accessible | pass |
| 2 | lock-unlock-relock preserves all accumulated bindings | pass |

**Example:** new bindings added after unlock are accessible
    Given val di = make_di()
    Then  expect(di.has("First")).to_equal(true)
    Then  expect(di.has("Second")).to_equal(true)

**Example:** lock-unlock-relock preserves all accumulated bindings
    Given val di = make_di()
    Then  expect(di.resolve("A")).to_equal("first")
    Then  expect(di.resolve("B")).to_equal("second")

### Scenario: env-var lock mechanism

| # | Example | Status |
|---|---------|--------|
| 1 | di_is_system_test_locked returns false normally | pass |
| 2 | env lock blocks bind_instance when system test active | pass |

**Example:** di_is_system_test_locked returns false normally
    Then  expect(di_is_system_test_locked()).to_equal(false)

**Example:** env lock blocks bind_instance when system test active
    Given val di = make_di()
    Then  expect(di.has("MockSvc")).to_equal(false)

## Feature: DI Lock: Phase 5 - System full DI lifecycle

### Scenario: complete register-lock-resolve cycle

| # | Example | Status |
|---|---------|--------|
| 1 | full DI lifecycle: register, lock, resolve, unlock, extend | pass |
| 2 | resolve_or covers missing services during operation | pass |
| 3 | has correctly reflects what is and is not registered | pass |

**Example:** full DI lifecycle: register, lock, resolve, unlock, extend
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(true)
    Then  expect(di.resolve("logger")).to_equal("console_logger")
    Then  expect(di.resolve("config")).to_equal("prod_config")
    Then  expect(di.resolve("parser")).to_equal("default_parser")
    Then  expect(di.has("extra")).to_equal(false)
    Then  expect(di.is_locked()).to_equal(false)
    Then  expect(di.resolve("extra")).to_equal("new_service")

**Example:** resolve_or covers missing services during operation
    Given val di = make_di()
    Given val logger = di.resolve_or("logger", "noop_logger")
    Given val tracer = di.resolve_or("tracer", "noop_tracer")
    Then  expect(logger).to_equal("syslog")
    Then  expect(tracer).to_equal("noop_tracer")

**Example:** has correctly reflects what is and is not registered
    Given val di = make_di()
    Then  expect(di.has("ServiceA")).to_equal(true)
    Then  expect(di.has("ServiceB")).to_equal(true)
    Then  expect(di.has("ServiceC")).to_equal(false)

### Scenario: env-var lock full flow

| # | Example | Status |
|---|---------|--------|
| 1 | env lock is_locked reflects env state then resets | pass |
| 2 | SIMPLE_DI_TEST=1 bypass allows registration in env-locked state | pass |

**Example:** env lock is_locked reflects env state then resets
    Given val di = make_di()
    Then  expect(di.is_locked()).to_equal(true)
    Given val di2 = make_di()
    Then  expect(di2.is_locked()).to_equal(false)

**Example:** SIMPLE_DI_TEST=1 bypass allows registration in env-locked state
    Given val di = make_di()
    Then  expect(di.has("TestMock")).to_equal(true)


