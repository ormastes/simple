# Extended Coverage JSON Format Specification

This document defines the extended coverage JSON format that enriches LLVM coverage data with Simple-specific metrics.

## Overview

The coverage system produces three types of output:

1. **System Test Coverage** - Public class/struct method coverage
2. **Integration Test Coverage** - Public function coverage
3. **Merged Coverage** - Combined branch/condition coverage

## JSON Format

### Root Structure

```json
{
  "version": "1.0",
  "timestamp": "2025-12-16T10:30:00Z",
  "source": {
    "llvm_coverage_file": "coverage.json",
    "public_api_file": "public_api.yml"
  },
  "summary": {
    "total_types": 15,
    "covered_types": 12,
    "type_coverage_percent": 80.0,
    "total_methods": 150,
    "covered_methods": 120,
    "method_coverage_percent": 80.0,
    "total_functions": 200,
    "covered_functions": 180,
    "function_coverage_percent": 90.0,
    "total_lines": 5000,
    "covered_lines": 4500,
    "line_coverage_percent": 90.0,
    "total_branches": 1000,
    "covered_branches": 800,
    "branch_coverage_percent": 80.0
  },
  "types": [...],
  "functions": [...],
  "files": [...]
}
```

### Type Coverage (System Tests)

```json
{
  "types": [
    {
      "name": "simple::compiler::Parser",
      "file": "src/compiler/src/parser.rs",
      "line_start": 50,
      "line_end": 500,
      "is_public": true,
      "kind": "struct",
      "methods": [
        {
          "name": "parse",
          "signature": "fn parse(&self, source: &str) -> Result<AST>",
          "line_start": 100,
          "line_end": 150,
          "is_public": true,
          "execution_count": 1250,
          "covered": true,
          "line_coverage": {
            "total": 50,
            "covered": 48,
            "percent": 96.0
          },
          "branch_coverage": {
            "total": 10,
            "covered": 8,
            "percent": 80.0
          }
        },
        {
          "name": "tokenize",
          "signature": "fn tokenize(&self) -> Vec<Token>",
          "line_start": 200,
          "line_end": 250,
          "is_public": true,
          "execution_count": 0,
          "covered": false,
          "line_coverage": {
            "total": 50,
            "covered": 0,
            "percent": 0.0
          },
          "branch_coverage": {
            "total": 5,
            "covered": 0,
            "percent": 0.0
          }
        }
      ],
      "summary": {
        "total_methods": 10,
        "covered_methods": 8,
        "method_coverage_percent": 80.0,
        "total_public_methods": 5,
        "covered_public_methods": 4,
        "public_method_coverage_percent": 80.0
      }
    }
  ]
}
```

### Function Coverage (Integration Tests)

```json
{
  "functions": [
    {
      "name": "simple::compiler::compile",
      "qualified_name": "simple_compiler::compile",
      "file": "src/compiler/src/lib.rs",
      "line_start": 50,
      "line_end": 100,
      "signature": "pub fn compile(source: &str) -> Result<Module>",
      "is_public": true,
      "is_exported": true,
      "execution_count": 500,
      "covered": true,
      "line_coverage": {
        "total": 50,
        "covered": 45,
        "percent": 90.0
      },
      "branch_coverage": {
        "total": 8,
        "covered": 6,
        "percent": 75.0
      }
    },
    {
      "name": "simple::compiler::internal_helper",
      "qualified_name": "simple_compiler::internal_helper",
      "file": "src/compiler/src/lib.rs",
      "line_start": 200,
      "line_end": 220,
      "signature": "fn internal_helper() -> bool",
      "is_public": false,
      "is_exported": false,
      "execution_count": 1000,
      "covered": true,
      "line_coverage": {
        "total": 20,
        "covered": 20,
        "percent": 100.0
      },
      "branch_coverage": {
        "total": 2,
        "covered": 2,
        "percent": 100.0
      }
    }
  ]
}
```

### File Coverage (Merged Data)

```json
{
  "files": [
    {
      "path": "src/compiler/src/lib.rs",
      "line_coverage": {
        "total": 500,
        "covered": 450,
        "percent": 90.0
      },
      "branch_coverage": {
        "total": 100,
        "covered": 80,
        "percent": 80.0
      },
      "function_coverage": {
        "total": 20,
        "covered": 18,
        "percent": 90.0
      },
      "regions": [
        {
          "line_start": 10,
          "col_start": 1,
          "line_end": 50,
          "col_end": 1,
          "execution_count": 100,
          "kind": "code"
        }
      ]
    }
  ]
}
```

## Output Files

The coverage tool generates three output files:

| File | Test Level | Metrics | Purpose |
|------|------------|---------|---------|
| `coverage_system.json` | System | Type/Method coverage | Public struct/class coverage |
| `coverage_integration.json` | Integration | Function coverage | Public function coverage |
| `coverage_merged.json` | All | Line/Branch coverage | Overall coverage report |

## Thresholds

```json
{
  "thresholds": {
    "system": {
      "type_coverage": 100.0,
      "method_coverage": 80.0
    },
    "integration": {
      "public_function_coverage": 100.0,
      "function_line_coverage": 80.0
    },
    "merged": {
      "line_coverage": 80.0,
      "branch_coverage": 70.0
    }
  }
}
```

## Public API Specification (Input)

The tool reads `public_api.yml` to determine which types and functions are public:

```yaml
# public_api.yml
types:
  simple::compiler::Parser:
    methods: [parse, tokenize, validate]
  simple::runtime::GcRuntime:
    methods: [new, collect, allocate]

functions:
  - simple::compiler::compile
  - simple::compiler::compile_file
  - simple::driver::run
  - simple::driver::run_file

exclude:
  - "*::tests::*"
  - "*::test_*"
```

## Command Line Interface

```bash
# Generate all coverage reports
simple-coverage generate \
  --llvm-cov coverage.json \
  --api public_api.yml \
  --output-dir target/coverage/

# Generate specific report
simple-coverage generate \
  --llvm-cov coverage.json \
  --api public_api.yml \
  --type system \
  --output coverage_system.json

# Check thresholds
simple-coverage check \
  --coverage coverage_merged.json \
  --threshold 80.0

# Print summary
simple-coverage summary \
  --coverage coverage_merged.json
```

## Integration with Makefile

```makefile
# Generate coverage with extended format
coverage-extended:
	cargo llvm-cov --workspace --json > $(COVERAGE_DIR)/llvm_raw.json
	simple-coverage generate \
		--llvm-cov $(COVERAGE_DIR)/llvm_raw.json \
		--api public_api.yml \
		--output-dir $(COVERAGE_DIR)

# System test coverage
coverage-system:
	cargo llvm-cov --test system --json > $(COVERAGE_DIR)/system_raw.json
	simple-coverage generate \
		--llvm-cov $(COVERAGE_DIR)/system_raw.json \
		--api public_api.yml \
		--type system \
		--output $(COVERAGE_DIR)/coverage_system.json

# Integration test coverage
coverage-integration:
	cargo llvm-cov --test integration --json > $(COVERAGE_DIR)/integration_raw.json
	simple-coverage generate \
		--llvm-cov $(COVERAGE_DIR)/integration_raw.json \
		--api public_api.yml \
		--type integration \
		--output $(COVERAGE_DIR)/coverage_integration.json
```

## Example Extended Output

```json
{
  "version": "1.0",
  "timestamp": "2025-12-16T10:30:00Z",
  "source": {
    "llvm_coverage_file": "target/coverage/llvm_raw.json",
    "public_api_file": "public_api.yml"
  },
  "summary": {
    "total_types": 25,
    "covered_types": 23,
    "type_coverage_percent": 92.0,
    "total_methods": 150,
    "covered_methods": 135,
    "method_coverage_percent": 90.0,
    "total_functions": 200,
    "covered_functions": 190,
    "function_coverage_percent": 95.0,
    "total_lines": 10000,
    "covered_lines": 9000,
    "line_coverage_percent": 90.0,
    "total_branches": 2000,
    "covered_branches": 1600,
    "branch_coverage_percent": 80.0
  },
  "types": [
    {
      "name": "simple_compiler::Parser",
      "file": "src/compiler/src/parser.rs",
      "is_public": true,
      "kind": "struct",
      "methods": [
        {
          "name": "new",
          "is_public": true,
          "execution_count": 500,
          "covered": true
        },
        {
          "name": "parse",
          "is_public": true,
          "execution_count": 500,
          "covered": true
        },
        {
          "name": "internal_parse",
          "is_public": false,
          "execution_count": 1500,
          "covered": true
        }
      ],
      "summary": {
        "total_methods": 3,
        "covered_methods": 3,
        "method_coverage_percent": 100.0
      }
    }
  ],
  "functions": [
    {
      "name": "compile",
      "qualified_name": "simple_compiler::compile",
      "is_public": true,
      "execution_count": 100,
      "covered": true
    }
  ],
  "uncovered": {
    "types": [],
    "methods": [
      {
        "type": "simple_compiler::Lexer",
        "method": "peek_ahead",
        "file": "src/compiler/src/lexer.rs",
        "line": 250
      }
    ],
    "functions": [
      {
        "name": "simple_compiler::deprecated_compile",
        "file": "src/compiler/src/lib.rs",
        "line": 500
      }
    ]
  }
}
```

## See Also

- [LLVM Coverage Design](llvm_coverage.md)
- [Test Policy](../test.md)
- [BDD Spec Framework](../spec/bdd_spec.md)
