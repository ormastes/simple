# di error cases
*Source:* `test/feature/usage/di_error_cases_spec.spl`

## Feature: DI Error Cases: locked container rejects bindings

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | bind_instance on locked container does not store value | pass |
| 2 | bind factory on locked container does not register | pass |
| 3 | bind_for_profile on locked container does not register | pass |
| 4 | locked container does not overwrite previously bound value | pass |
| 5 | is_locked returns true after explicit lock | pass |
| 6 | is_locked returns false after unlock | pass |

**Example:** bind_instance on locked container does not store value
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.has("new_key")).to_equal(false)

**Example:** bind factory on locked container does not register
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.has("FactoryKey")).to_equal(false)

**Example:** bind_for_profile on locked container does not register
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.has("ProfileKey")).to_equal(false)

**Example:** locked container does not overwrite previously bound value
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.resolve("Service")).to_equal("original")

**Example:** is_locked returns true after explicit lock
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.is_locked()).to_equal(false)
    Then  expect(di.is_locked()).to_equal(true)

**Example:** is_locked returns false after unlock
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.is_locked()).to_equal(true)
    Then  expect(di.is_locked()).to_equal(false)

## Feature: DI Error Cases: missing key fallback

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | resolve_or returns default text for missing key | pass |
| 2 | resolve_or returns default integer for missing key | pass |
| 3 | has returns false for missing key | pass |
| 4 | resolve_or returns bound value when key exists | pass |
| 5 | has returns true after bind_instance | pass |

**Example:** resolve_or returns default text for missing key
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Given val result = di.resolve_or("nonexistent_key", "default_val")
    Then  expect(result).to_equal("default_val")

**Example:** resolve_or returns default integer for missing key
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Given val result = di.resolve_or("missing_int", 42)
    Then  expect(result).to_equal(42)

**Example:** has returns false for missing key
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.has("definitely_not_there")).to_equal(false)

**Example:** resolve_or returns bound value when key exists
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Given val result = di.resolve_or("existing", "should_not_be_used")
    Then  expect(result).to_equal("found_value")

**Example:** has returns true after bind_instance
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.has("present")).to_equal(true)

## Feature: DI Error Cases: edge cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | empty string key can be stored and retrieved | pass |
| 2 | overwriting key keeps the latest value | pass |
| 3 | multiple distinct keys are independent | pass |
| 4 | singleton is resolved from singletons not bindings | pass |
| 5 | factory binding is callable after bind | pass |

**Example:** empty string key can be stored and retrieved
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.resolve("")).to_equal("empty_key_val")

**Example:** overwriting key keeps the latest value
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.resolve("key")).to_equal("second")

**Example:** multiple distinct keys are independent
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.resolve("a")).to_equal("val_a")
    Then  expect(di.resolve("b")).to_equal("val_b")

**Example:** singleton is resolved from singletons not bindings
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.has("svc")).to_equal(true)
    Then  expect(di.resolve("svc")).to_equal("singleton_val")

**Example:** factory binding is callable after bind
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.has("computed")).to_equal(true)
    Given val result = di.resolve("computed")
    Then  expect(result).to_equal("computed_result")

## Feature: DI Error Cases: resolve works through lock

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | resolve_or for existing key works when locked | pass |
| 2 | resolve_or for missing key returns default when locked | pass |
| 3 | resolve for pre-lock binding works after lock | pass |

**Example:** resolve_or for existing key works when locked
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Given val result = di.resolve_or("Config", "default")
    Then  expect(result).to_equal("prod-config")

**Example:** resolve_or for missing key returns default when locked
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Given val result = di.resolve_or("NotPresent", "fallback")
    Then  expect(result).to_equal("fallback")

**Example:** resolve for pre-lock binding works after lock
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.resolve("Backend")).to_equal("production-backend")

## Feature: DI Error Cases: env-var lock rejects bindings

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | bind rejected when SIMPLE_SYSTEM_TEST=1 and SIMPLE_DI_TEST not set | pass |
| 2 | bind allowed when SIMPLE_DI_TEST=1 bypasses env lock | pass |
| 3 | di_is_system_test_locked returns false when env not set | pass |

**Example:** bind rejected when SIMPLE_SYSTEM_TEST=1 and SIMPLE_DI_TEST not set
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.has("MockSvc")).to_equal(false)

**Example:** bind allowed when SIMPLE_DI_TEST=1 bypasses env lock
    Given val di = DiContainer(bindings: {}, singletons: {}, profile: "dev", all_bindings: [], locked: false)
    Then  expect(di.has("TestMock")).to_equal(true)

**Example:** di_is_system_test_locked returns false when env not set
    Then  expect(di_is_system_test_locked()).to_equal(false)


