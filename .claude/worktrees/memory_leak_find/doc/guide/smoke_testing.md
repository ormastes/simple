# Smoke Testing Guide

**Status:** Implemented (Phase 2)
**Library:** `std.testing.deployment`

## Overview

Smoke testing provides post-deployment verification by running critical health checks. It ensures basic functionality works after deployment, with automatic retries for flaky tests.

## Quick Start

### Basic Smoke Test

```simple
import std.testing.deployment as smoke

fn main():
    val suite = smoke.SmokeTestSuite.new_default()
        .test("homepage loads", \:
            http.get("https://myapp.com/").status == 200
        )
        .test("database connected", \:
            db.ping().is_ok()
        )
        .test("API health check", \:
            val resp = http.get("https://myapp.com/api/health")
            resp.status == 200 and resp.body["status"] == "ok"
        )

    val results = suite.run()

    for result in results:
        print result.format()

    if not suite.all_passed(results):
        print "\n❌ Smoke tests failed! Rolling back..."
        rollback_deployment()
        exit(1)

    print "\n✅ All smoke tests passed!"
```

**Output:**
```
✅ homepage loads (234.56ms)
✅ database connected (12.34ms)
✅ API health check (156.78ms)

✅ All smoke tests passed!
```

## Configuration

### Default Configuration

```simple
val config = SmokeTestConfig.default()
# timeout_secs: 30.0
# retry_attempts: 3
# retry_delay_secs: 5.0
# fail_fast: true
```

### Custom Configuration

```simple
val config = SmokeTestConfig(
    timeout_secs: 60.0,      # Longer timeout
    retry_attempts: 5,        # More retries
    retry_delay_secs: 10.0,   # Longer delay
    fail_fast: false          # Run all tests
)

val suite = smoke.SmokeTestSuite.new(config)
```

## Retry Logic

### How Retries Work

Tests automatically retry on failure:

1. **First attempt:** Run test
2. **If fails:** Wait `retry_delay_secs`
3. **Second attempt:** Run test again
4. **Repeat** up to `retry_attempts` times
5. **If all fail:** Report failure

### Example: Flaky Network Test

```simple
var attempt_count = 0

val suite = smoke.SmokeTestSuite.new_default()
    .test("flaky API", \:
        attempt_count = attempt_count + 1
        print "Attempt {attempt_count}..."

        # Simulate flaky network (passes on 2nd try)
        attempt_count >= 2
    )

val results = suite.run()
# Output:
# Attempt 1...
# (wait 5 seconds)
# Attempt 2...
# ✅ flaky API (5234.56ms)
```

### When to Use Retries

**Good use cases:**
- Network requests (temporary failures)
- Database connections (connection pool exhaustion)
- Service mesh (transient errors)

**Bad use cases:**
- Logic errors (will never pass)
- Permanent failures (waste time)

## Fail Fast

### Enabled (Default)

Stops on first failure:

```simple
val config = SmokeTestConfig.default()  # fail_fast: true

val suite = smoke.SmokeTestSuite.new(config)
    .test("critical", \: check_critical())    # Fails!
    .test("optional", \: check_optional())     # Never runs
```

**When to use:**
- Critical path testing
- Quick feedback needed
- Later tests depend on earlier ones

### Disabled

Runs all tests regardless of failures:

```simple
val config = SmokeTestConfig(
    timeout_secs: 30.0,
    retry_attempts: 3,
    retry_delay_secs: 5.0,
    fail_fast: false  # Run all tests
)

val suite = smoke.SmokeTestSuite.new(config)
    .test("service_a", \: check_a())  # Fails
    .test("service_b", \: check_b())  # Still runs
    .test("service_c", \: check_c())  # Still runs
```

**When to use:**
- Comprehensive health check
- Multiple independent services
- Collecting all failures for debugging

## Real-World Examples

### Example 1: Web Application

```simple
import std.testing.deployment as smoke
import std.http

fn check_homepage() -> bool:
    val resp = http.get("https://myapp.com/")
    resp.status == 200 and resp.body.contains("<html>")

fn check_login() -> bool:
    val resp = http.post("https://myapp.com/login", {
        username: "health_check",
        password: "test123"
    })
    resp.status == 200

fn check_api() -> bool:
    val resp = http.get("https://myapp.com/api/v1/health")
    resp.status == 200 and resp.body["status"] == "healthy"

fn main():
    val suite = smoke.SmokeTestSuite.new_default()
        .test("homepage loads", check_homepage)
        .test("login works", check_login)
        .test("API responds", check_api)

    val results = suite.run()

    if not suite.all_passed(results):
        # Rollback deployment
        run_command("kubectl rollout undo deployment/myapp")
        exit(1)
```

### Example 2: Microservices

```simple
import std.testing.deployment as smoke

fn check_user_service() -> bool:
    val resp = http.get("https://user-service/health")
    resp.status == 200

fn check_order_service() -> bool:
    val resp = http.get("https://order-service/health")
    resp.status == 200

fn check_payment_service() -> bool:
    val resp = http.get("https://payment-service/health")
    resp.status == 200

fn check_end_to_end() -> bool:
    # Create test order
    val user_id = create_test_user()
    val order_id = create_test_order(user_id)
    val payment = process_test_payment(order_id)

    cleanup_test_data(user_id, order_id)
    payment.status == "success"

fn main():
    val config = SmokeTestConfig(
        timeout_secs: 60.0,     # E2E test needs more time
        retry_attempts: 3,
        retry_delay_secs: 10.0,
        fail_fast: false         # Check all services
    )

    val suite = smoke.SmokeTestSuite.new(config)
        .test("User service", check_user_service)
        .test("Order service", check_order_service)
        .test("Payment service", check_payment_service)
        .test("End-to-end flow", check_end_to_end)

    val results = suite.run()

    # Report to Slack/PagerDuty
    if not suite.all_passed(results):
        notify_oncall(results)
```

### Example 3: Database Migration

```simple
import std.testing.deployment as smoke

fn check_schema_version() -> bool:
    val version = db.query("SELECT version FROM schema_version").first()
    version == "2.5.0"

fn check_new_columns() -> bool:
    # Verify migration added new columns
    val columns = db.query("SHOW COLUMNS FROM users")
    columns.any(\c: c.name == "created_at") and
    columns.any(\c: c.name == "updated_at")

fn check_data_integrity() -> bool:
    # Verify data wasn't corrupted
    val count = db.query("SELECT COUNT(*) FROM users").first()
    count > 0 and count == expected_user_count

fn main():
    val suite = smoke.SmokeTestSuite.new_default()
        .test("Schema version updated", check_schema_version)
        .test("New columns exist", check_new_columns)
        .test("Data integrity", check_data_integrity)

    val results = suite.run()

    if not suite.all_passed(results):
        print "Migration verification failed!"
        print "Restore from backup? (y/n)"
        # ...
```

## Integration Patterns

### Pattern 1: CI/CD Pipeline

```yaml
# .github/workflows/deploy.yml
name: Deploy

on:
  push:
    branches: [main]

jobs:
  deploy:
    runs-on: ubuntu-latest
    steps:
      - name: Deploy to staging
        run: kubectl apply -f k8s/staging/

      - name: Wait for rollout
        run: kubectl rollout status deployment/myapp

      - name: Run smoke tests
        run: simple smoke tests/staging_smoke.spl

      - name: Promote to production
        if: success()
        run: kubectl apply -f k8s/production/

      - name: Run production smoke tests
        run: simple smoke tests/production_smoke.spl

      - name: Rollback on failure
        if: failure()
        run: kubectl rollout undo deployment/myapp
```

### Pattern 2: Blue-Green Deployment

```simple
import std.testing.deployment as smoke

fn deploy_blue_green():
    # Deploy to "green" environment
    print "Deploying to green environment..."
    deploy_to_environment("green")

    # Run smoke tests on green
    print "Running smoke tests on green..."
    val suite = smoke.SmokeTestSuite.new_default()
        .test("green: homepage", \:
            http.get("https://green.myapp.com/").status == 200
        )
        .test("green: API", \:
            http.get("https://green.myapp.com/api/health").status == 200
        )

    val results = suite.run()

    if not suite.all_passed(results):
        print "❌ Green environment failed smoke tests!"
        teardown_environment("green")
        return

    # Switch traffic to green
    print "✅ Smoke tests passed, switching traffic to green..."
    update_load_balancer("green")

    # Keep blue for rollback
    print "Blue environment kept for rollback"
```

### Pattern 3: Canary Deployment

```simple
import std.testing.deployment as smoke

fn canary_deploy():
    # Deploy canary (5% traffic)
    deploy_canary("v2.0.0", traffic_percentage: 5)

    # Run smoke tests
    val suite = smoke.SmokeTestSuite.new_default()
        .test("canary responding", \:
            http.get("https://canary.myapp.com/").status == 200
        )

    val results = suite.run()

    if not suite.all_passed(results):
        print "Canary failed, rolling back..."
        rollback_canary()
        return

    # Monitor metrics for 5 minutes
    print "Monitoring canary metrics..."
    time.sleep(300.0)

    if error_rate_acceptable() and latency_acceptable():
        # Increase traffic gradually
        increase_canary_traffic(25)  # → 25%
        time.sleep(300.0)

        increase_canary_traffic(50)  # → 50%
        time.sleep(300.0)

        increase_canary_traffic(100) # → 100%
        print "✅ Canary deployment complete!"
    else:
        print "❌ Canary metrics degraded, rolling back..."
        rollback_canary()
```

## CLI Usage

### Basic Usage

```bash
# Run smoke tests
simple smoke tests/smoke_tests.spl

# Exit code 0 if all pass, 1 if any fail
```

### With Configuration

```bash
# Custom timeout
simple smoke --timeout 60 tests/smoke_tests.spl

# More retries
simple smoke --retry 5 --delay 10 tests/smoke_tests.spl

# Run all tests (don't fail fast)
simple smoke --no-fail-fast tests/smoke_tests.spl
```

## Best Practices

### 1. Test Critical Paths Only

❌ **Don't test everything:**
```simple
.test("admin panel loads", \: ...)
.test("user settings loads", \: ...)
.test("help page loads", \: ...)
```

✅ **Test critical functionality:**
```simple
.test("users can log in", \: ...)
.test("checkout works", \: ...)
.test("payment processing", \: ...)
```

### 2. Keep Tests Fast

❌ **Slow test:**
```simple
.test("database backup", \:
    backup_database()  # Takes 10 minutes!
    verify_backup()
)
```

✅ **Fast test:**
```simple
.test("database responds", \:
    db.ping().is_ok()  # Takes 10ms
)
```

### 3. Make Tests Idempotent

❌ **Not idempotent:**
```simple
.test("create user", \:
    create_user("test@example.com")  # Fails on 2nd run!
)
```

✅ **Idempotent:**
```simple
.test("create user", \:
    delete_user_if_exists("test@example.com")
    create_user("test@example.com")
    cleanup_user("test@example.com")
    true
)
```

### 4. Use Descriptive Names

❌ **Vague:**
```simple
.test("test1", \: ...)
.test("check API", \: ...)
```

✅ **Descriptive:**
```simple
.test("homepage returns 200 OK", \: ...)
.test("API /health returns healthy status", \: ...)
```

## Troubleshooting

### Problem: Tests Timeout

**Symptoms:**
```
⏱️  database connected (timed out)
```

**Solutions:**
1. Increase timeout: `timeout_secs: 60.0`
2. Check if service is actually slow
3. Verify network connectivity
4. Check firewall rules

### Problem: Flaky Tests

**Symptoms:**
Tests pass sometimes, fail other times.

**Solutions:**
1. Increase retry attempts
2. Add delays between retries
3. Fix underlying flakiness (better than retrying)
4. Use health check endpoints (not homepage)

### Problem: All Tests Fail

**Symptoms:**
```
❌ homepage loads (failed after 3 attempts)
❌ database connected (failed after 3 attempts)
❌ API health check (failed after 3 attempts)
```

**Solutions:**
1. Check if deployment actually completed
2. Verify network connectivity
3. Check service logs
4. Manually test endpoints

## Examples

See `simple/std_lib/test/unit/testing/smoke_test_spec.spl` for more examples.

## API Reference

### Types

**`SmokeTestConfig`**
- Configuration for smoke tests
- Methods: `default()`

**`SmokeTestResult`**
- Result of a single test
- Variants: `Pass`, `Fail`, `Timeout`
- Methods: `is_pass()`, `is_fail()`, `is_timeout()`, `format()`

**`SmokeTestSuite`**
- Collection of smoke tests
- Methods: `new()`, `new_default()`, `test()`, `run()`, `all_passed()`

## Further Reading

- [Blue-Green Deployment](https://martinfowler.com/bliki/BlueGreenDeployment.html)
- [Canary Deployment](https://martinfowler.com/bliki/CanaryRelease.html)
- [Smoke Testing - Wikipedia](https://en.wikipedia.org/wiki/Smoke_testing_(software))
