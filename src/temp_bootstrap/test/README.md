# Simple Language Tests

This directory contains tests written in Simple language using the BDD framework.

## Directory Structure

```
test/
├── __init__.spl          # Root test environment (std.spec.* imports)
├── environment/          # Test runtime orchestration
│   ├── __init__.spl      # Environment configuration
│   ├── bootstrap.spl     # Process-level bootstrap
│   ├── fixtures/         # Test fixtures and data
│   └── helpers/          # Shared test helpers
├── unit/                 # Unit tests (Simple .spl)
│   ├── __init__.spl      # Unit test configuration
│   └── **/*_spec.spl     # Fast isolated tests
├── integration/          # Integration tests (Simple .spl)
│   ├── __init__.spl      # Integration test configuration
│   └── **/*_spec.spl     # Public function tests
└── system/               # System tests (Simple .spl)
    ├── __init__.spl      # System test configuration
    └── **/*_spec.spl     # Public class/struct tests
```

## Test Levels

### Unit Tests (`unit/`)
- **Goal**: Fast, isolated tests for internal behavior
- **Target**: Private/internal functions, pure logic units, small modules
- **Coverage**: Branch/condition coverage (merged with environment)
- **Command**: `make test-unit`

### Integration Tests (`integration/`)
- **Goal**: Validate public functions and module boundaries
- **Target**: Exported functions and module-level APIs
- **Coverage**: Public function touch (100%)
- **Command**: `make test-integration`

### System Tests (`system/`)
- **Goal**: Validate public types and end-to-end behavior
- **Target**: Public classes/structs with business logic
- **Coverage**: Public class/struct touch (100%)
- **Command**: `make test-system`

### Environment Tests (`environment/`)
- **Goal**: Test runtime orchestration
- **Target**: HAL, external dependencies, fixtures
- **Coverage**: Branch/condition (merged with unit)
- **Command**: `make test-environment`

## Writing Tests

Tests use the BDD framework (RSpec-style):

```simple
# example_spec.spl
import test.unit.*

describe "Calculator":
    it "adds two numbers":
        expect(add(2, 3)).to eq(5)
    
    it "subtracts two numbers":
        expect(subtract(5, 3)).to eq(2)
```

## Running Tests

```bash
# Run all tests
make test

# Run specific test level
make test-unit
make test-integration
make test-system
make test-environment

# Run with coverage
make coverage-all
```

## Coverage Reports

Coverage is tracked separately for each test level:

- **Unit + Environment**: Branch/condition coverage (merged)
- **Integration**: Public function touch (100% required)
- **System**: Public class/struct touch (100% required)

See `doc/test.md` for detailed coverage policy.
