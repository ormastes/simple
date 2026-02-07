# Test Attributes Implementation Plan

**Feature:** Test attributes for configuration and metadata
**Priority:** MEDIUM
**Impact:** 49 skipped tests (6% of @skip markers)
**Estimated Effort:** 1-2 sprints
**Status:** Planning

---

## Overview

Test attributes allow adding metadata and configuration to test cases without cluttering test logic.

### Syntax

```simple
#[timeout(5000)]
#[retry(3)]
#[tag("slow", "integration")]
it "performs complex database operation":
    # test code

#[skip("Feature not implemented")]
it "tests future feature":
    # test code

#[flaky]
#[timeout(10000)]
it "tests network operation":
    # test code
```

---

## Required Attributes

### Core Attributes

1. **`#[timeout(ms)]`** - Set test timeout
   ```simple
   #[timeout(30000)]  # 30 seconds
   it "slow database query":
       execute_long_query()
   ```

2. **`#[retry(count)]`** - Retry flaky tests
   ```simple
   #[retry(3)]  # Retry up to 3 times
   it "flaky network test":
       check external_api_call()
   ```

3. **`#[tag(...)]`** - Categorize tests
   ```simple
   #[tag("slow", "integration", "database")]
   it "full database integration":
       # test code
   ```

4. **`#[skip(reason)]`** - Skip test with reason
   ```simple
   #[skip("Requires GPU")]
   it "CUDA kernel test":
       # test code
   ```

5. **`#[flaky]`** - Mark known flaky test
   ```simple
   #[flaky]
   it "timing-sensitive test":
       # test code
   ```

### Advanced Attributes

6. **`#[parallel]` / `#[serial]`** - Control parallelization
   ```simple
   #[serial]  # Must run alone
   it "modifies global state":
       # test code
   ```

7. **`#[fixture(name)]`** - Use specific fixture
   ```simple
   #[fixture("large_dataset")]
   it "tests with big data":
       # test code
   ```

8. **`#[only]`** - Run only this test
   ```simple
   #[only]  # Focus mode
   it "debugging specific issue":
       # test code
   ```

---

## Implementation Phases

### Phase 1: Parser Support (1 week)

**AST Changes:**

```simple
struct TestCase:
    name: text
    attributes: [Attribute]  # NEW
    body: Block

struct Attribute:
    name: text
    args: [Expr]
```

**Parser changes:**

```simple
fn parse_test_case() -> TestCase:
    var attributes = []

    # Parse attributes
    while current_token() == Hash:
        consume(Hash)
        consume(LBracket)
        val attr_name = expect_identifier()
        var attr_args = []

        if check(LParen):
            consume(LParen)
            # Parse argument list
            if not check(RParen):
                loop:
                    attr_args.push(parse_expr())
                    if not check(Comma):
                        break
                    consume(Comma)
            consume(RParen)

        consume(RBracket)
        attributes.push(Attribute(name: attr_name, args: attr_args))

    # Parse test case (it, test, example, etc.)
    # ...
```

---

### Phase 2: Test Framework Integration (1 week)

**Attribute Processing:**

```simple
# In test runner
fn run_test_case(test: TestCase) -> TestResult:
    # Process attributes
    var timeout = DEFAULT_TIMEOUT
    var retry_count = 1
    var skip_reason = nil
    var tags = []

    for attr in test.attributes:
        match attr.name:
            "timeout":
                timeout = attr.args[0].as_int()
            "retry":
                retry_count = attr.args[0].as_int()
            "skip":
                skip_reason = attr.args[0].as_string()
                return TestResult.Skipped(skip_reason)
            "tag":
                for arg in attr.args:
                    tags.push(arg.as_string())
            "flaky":
                # Mark test as flaky in database
                mark_flaky(test.name)

    # Run test with timeout and retries
    for attempt in 1..=retry_count:
        val result = run_with_timeout(test.body, timeout)
        if result.passed or attempt == retry_count:
            return result
        # Retry on failure

    result
```

---

### Phase 3: Database Integration (3 days)

**Store attributes in test database:**

```sdn
test_attributes |test_id, attr_name, attr_value|
    1, timeout, 5000
    1, tag, "slow"
    1, tag, "integration"
    2, retry, 3
    2, flaky, true
```

**Query by attributes:**

```simple
# Find all slow tests
slow_tests = test_db.query()
    .where("attr_name", "tag")
    .where("attr_value", "slow")
    .execute()
```

---

### Phase 4: CLI Integration (2 days)

**Filter tests by attributes:**

```bash
# Run only tests with specific tag
simple test --tag=integration

# Exclude flaky tests
simple test --exclude-tag=flaky

# Run tests with timeout > 10s
simple test --filter='timeout>10000'

# List tests by attribute
simple test --list --filter='tag:slow'
```

---

## Standard Library Support

```simple
# src/std/testing/attributes.spl

# Attribute validation
fn validate_timeout(value: i64) -> bool:
    value > 0 and value <= 3600000  # Max 1 hour

fn validate_retry(count: i64) -> bool:
    count >= 1 and count <= 10  # Max 10 retries

# Attribute application
fn apply_timeout(test: Test, timeout_ms: i64):
    test.config.timeout = timeout_ms

fn apply_retry(test: Test, count: i64):
    test.config.retry_count = count

# Query by attributes
fn find_tests_with_tag(tests: [Test], tag: text) -> [Test]:
    tests.filter(\t: t.has_tag(tag))
```

---

## Testing Plan

1. **Attribute parsing**
   - Parse single attribute
   - Parse multiple attributes
   - Parse attributes with arguments
   - Parse attributes with multiple arguments

2. **Attribute application**
   - Timeout enforcement
   - Retry logic
   - Tag filtering
   - Skip handling

3. **Integration tests**
   - Run tests with various attributes
   - Verify timeout works
   - Verify retry works
   - Filter by tags

---

## Success Criteria

1. ✅ Parser accepts `#[attr]` syntax
2. ✅ Attributes stored in test metadata
3. ✅ Timeout attribute enforced
4. ✅ Retry attribute works
5. ✅ Tag filtering works
6. ✅ Skip attribute honored
7. ✅ 49 skipped tests pass
8. ✅ Documentation complete

---

## Timeline

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| 1. Parser | 1 week | Attribute parsing works |
| 2. Framework | 1 week | Attributes processed |
| 3. Database | 3 days | Attributes stored/queryable |
| 4. CLI | 2 days | Filter by attributes |
| **Total** | **3 weeks** | **Feature complete** |

---

## Dependencies

- **Blocker:** None
- **Enhanced by:** Test database system (already implemented)
- **Enables:** Better test organization, flaky test handling, test categorization
