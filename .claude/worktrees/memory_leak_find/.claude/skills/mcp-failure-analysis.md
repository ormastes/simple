# MCP Failure Analysis Skills

Quick reference for using MCP tools to analyze test failures and prioritize feature implementation.

## Tools Available

### 1. query_failed_test_details

Get detailed information about failed tests.

**Usage:**
```
query_failed_test_details(
    limit: 20,
    include_error: true,
    include_features: true,
    category: "Unit"
)
```

**Returns:**
- Test name, file, category, error type
- Optional: truncated error message
- Optional: needed features list

### 2. analyze_failures

Analyze all failure patterns and rank features by priority.

**Usage:**
```
analyze_failures()
```

**Returns:**
- Total failed test count
- Breakdown by error type with percentages
- Top 20 needed features with priority (🔴 Critical, 🟠 High, 🟡 Medium, 🟢 Low)

**Priority Levels:**
- 🔴 Critical: 10+ tests blocked
- 🟠 High: 5-9 tests blocked
- 🟡 Medium: 2-4 tests blocked
- 🟢 Low: 1 test blocked

### 3. find_features_for_failed_tests

Cross-reference failed tests with feature database.

**Usage:**
```
find_features_for_failed_tests()
```

**Returns:**
- Feature name and status (planned/in_progress/complete)
- Number of tests blocked
- List of affected tests (first 5, with count of additional)

## Workflow

### Step 1: Analyze Current Situation

```bash
# Get overview of all failures
analyze_failures()
```

This shows:
- How many tests are failing
- What types of errors are most common
- Which features would unblock the most tests

### Step 2: Get Details on Specific Category

```bash
# Focus on Unit tests with detailed error messages
query_failed_test_details(
    category: "Unit",
    include_features: true,
    limit: 30
)
```

### Step 3: Check Feature Status

```bash
# See which features are already planned/in-progress
find_features_for_failed_tests()
```

### Step 4: Prioritize Implementation

Based on the analysis:
1. Focus on 🔴 Critical features (10+ tests blocked)
2. Check if feature is already in feature_db.sdn
3. Implement highest-impact features first

## Error Types Reference

| Error Type | Meaning | Example |
|-----------|---------|---------|
| `parse_error` | Syntax errors | "expected Fn, found Static" |
| `semantic_error` | Type/identifier errors | "function not found" |
| `file_not_found` | Missing test files | "No such file or directory" |
| `timeout` | Test performance | "Test timed out after 30s" |
| `utf8_error` | File encoding | "invalid UTF-8" |
| `unknown_error` | Unrecognized | Any other error |

## Feature Extraction Patterns

The tools automatically detect these needed features from error messages:

**Parser Features:**
- `static_fields` - "expected Fn, found Static"
- `default_parameters` - "expected expression, found Default"
- `matrix_multiplication` - "expected expression, found At"
- `xor_keyword` - "expected identifier, found Xor"
- `dict_literal_syntax` - "expected Comma, found Colon"
- `list_comprehension` - "expected expression, found For"
- `implicit_val_var` - "expected expression, found Assign"
- and 10+ more...

**Semantic Features:**
- `string_char_at_method` - "method `char_at` not found"
- `mutability_checking` - "cannot modify ... in immutable fn"

## Tips

### For Quick Triage

```bash
# Show only parse errors in System tests
query_failed_test_details(
    category: "System",
    include_error: false,
    limit: 10
)
```

### For Feature Planning

```bash
# Get comprehensive analysis
analyze_failures()
find_features_for_failed_tests()
```

Then:
1. Cross-reference priorities
2. Check feature database for status
3. Implement highest-impact planned features

### For Debugging Specific Failures

```bash
# Get full error messages for Integration tests
query_failed_test_details(
    category: "Integration",
    include_error: true,
    include_features: true
)
```

## Database Files

The tools read from:
- `doc/test/test_db.sdn` - Test execution results
- `doc/feature/feature_db.sdn` - Feature implementation status

These are automatically updated by `simple test` and other commands.

## Implementation Status

**Files Modified:**
- `src/lib/std/src/mcp/simple_lang/db_tools.spl` (+400 lines)

**Tests Created:**
- `test/lib/std/unit/mcp/failure_analysis_spec.spl` (23 tests, 14 passing)

**Tools Added:**
- 3 new MCP tools
- 4 new helper functions
- Full error classification system

## See Also

- Full documentation: `doc/report/mcp_failure_analysis_implementation.md`
- MCP README: `src/lib/std/src/mcp/README.md`
- Test framework: `doc/spec/testing_framework_spec.md`
