# Dependency Injection Specification
*Source:* `test/feature/usage/di_injection_spec.spl`
**Feature IDs:** #DI-INJ-001 to #DI-INJ-007  |  **Category:** Runtime | Dependency Injection  |  **Status:** Implemented

## Overview


**Tags:** di, integration

Integration tests for DI Container with realistic service patterns.
Tests focus on scenarios not covered by unit tests.

## Feature: Service with Dependencies

Tests realistic service patterns where services depend on other services.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates service with repository dependency | pass |
| 2 | chains multiple text dependencies | pass |

**Example:** creates service with repository dependency
    Given val repo = Repository(name: "users")
    Given val service = UserService(repo: repo)
    Then  expect service.repo.name == "users"

**Example:** chains multiple text dependencies
    Given var container = TextContainer.empty()
    Given val config = container.get("DbConfig")
    Then  expect config.?
    Given val pool = "pool:{config.unwrap()}"
    Given val pool_value = container.get("ConnectionPool")
    Then  expect pool_value.?
    Given val app = "app using {pool_value.unwrap()}"
    Then  expect app == "app using pool:db://localhost:5432"

## Feature: Profile-Based Configuration

Tests that profile patterns work correctly.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | profile enum converts to text | pass |
| 2 | profile enum parses from text | pass |
| 3 | profile defaults to dev for unknown | pass |
| 4 | all profiles have unique names | pass |

**Example:** profile enum converts to text
    Given val p = Profile.Test
    Then  expect p.name() == "test"

**Example:** profile enum parses from text
    Given val p = Profile.from_text("prod")
    Then  expect p.name() == "prod"

**Example:** profile defaults to dev for unknown
    Given val p = Profile.from_text("unknown")
    Then  expect p.name() == "dev"

**Example:** all profiles have unique names
    Given val test = Profile.Test.name()
    Given val dev = Profile.Dev.name()
    Given val prod = Profile.Prod.name()
    Given val sdn = Profile.Sdn.name()
    Then  expect test != dev
    Then  expect dev != prod
    Then  expect prod != sdn

## Feature: Container Binding Pattern

Tests the container binding and retrieval pattern.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | stores and retrieves values | pass |
| 2 | has returns true for existing keys | pass |
| 3 | get returns None for missing keys | pass |
| 4 | set overwrites existing values | pass |

**Example:** stores and retrieves values
    Given var container = TextContainer.empty()
    Given val result = container.get("service")
    Then  expect result.?
    Then  expect result.unwrap() == "my_service"

**Example:** has returns true for existing keys
    Given var container = TextContainer.empty()
    Then  expect container.has("key")
    Then  expect not container.has("missing")

**Example:** get returns None for missing keys
    Given val container = TextContainer.empty()
    Given val result = container.get("missing")
    Then  expect not result.?

**Example:** set overwrites existing values
    Given var container = TextContainer.empty()
    Given val result = container.get("key")
    Then  expect result.?
    Then  expect result.unwrap() == "second"

## Feature: DI Error Handling Pattern

Tests Result-based error handling for DI resolution.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | returns Ok for existing binding | pass |
| 2 | returns Err for missing binding | pass |

**Example:** returns Ok for existing binding
    Given val data: Dict<text, text> = {"Service": "instance"}
    Given val result = resolve(data, "Service")
    Then  expect result.ok.?
    Then  expect result.unwrap() == "instance"

**Example:** returns Err for missing binding
    Given val data: Dict<text, text> = {}
    Given val result = resolve(data, "Missing")
    Then  expect result.err.?
    Given val err_msg = result.unwrap_err()
    Then  expect err_msg.starts_with("No binding")

## Feature: @inject Decorator Recognition

Tests that @inject decorator is recognized by the parser/HIR.
    Note: Full runtime injection requires interpreter support (future).

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | function with @inject is parsed | pass |
| 2 | class method with @inject is parsed | pass |

**Example:** function with @inject is parsed
    Then  expect create_service("test") == "service:test"

**Example:** class method with @inject is parsed
    Given val db = Database.create("db://localhost")
    Then  expect db.connection == "db://localhost"


