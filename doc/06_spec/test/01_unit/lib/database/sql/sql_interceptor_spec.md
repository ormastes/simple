# Sql Interceptor Specification

> 1. var ti = TimingInterceptor new

<!-- sdn-diagram:id=sql_interceptor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sql_interceptor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sql_interceptor_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sql_interceptor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sql Interceptor Specification

## Scenarios

### TimingInterceptor

#### after_execute

#### records slow queries above threshold

1. var ti = TimingInterceptor new
2. ti after execute
   - Expected: slow.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ti = TimingInterceptor.new(100)
ti.after_execute("SELECT * FROM users", 150, true)
val slow = ti.slow_queries
expect(slow.len()).to_equal(1)
expect(slow[0]).to_contain("SELECT * FROM users")
expect(slow[0]).to_contain("150ms")
```

</details>

#### does not record queries below threshold

1. var ti = TimingInterceptor new
2. ti after execute
   - Expected: slow.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ti = TimingInterceptor.new(100)
ti.after_execute("SELECT 1", 50, true)
val slow = ti.slow_queries
expect(slow.len()).to_equal(0)
```

</details>

#### records query at exact threshold

1. var ti = TimingInterceptor new
2. ti after execute
   - Expected: slow.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ti = TimingInterceptor.new(100)
ti.after_execute("SELECT 1", 100, true)
val slow = ti.slow_queries
expect(slow.len()).to_equal(1)
```

</details>

#### records multiple slow queries

1. var ti = TimingInterceptor new
2. ti after execute
3. ti after execute
4. ti after execute
   - Expected: slow.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ti = TimingInterceptor.new(50)
ti.after_execute("query1", 60, true)
ti.after_execute("query2", 70, true)
ti.after_execute("fast_query", 10, true)
val slow = ti.slow_queries
expect(slow.len()).to_equal(2)
```

</details>

#### after_query

#### records slow SELECT queries

1. var ti = TimingInterceptor new
2. ti after query
   - Expected: slow.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ti = TimingInterceptor.new(100)
ti.after_query("SELECT * FROM users", 200, 50)
val slow = ti.slow_queries
expect(slow.len()).to_equal(1)
expect(slow[0]).to_contain("QUERY")
expect(slow[0]).to_contain("200ms")
expect(slow[0]).to_contain("50 rows")
```

</details>

#### does not record fast SELECT queries

1. var ti = TimingInterceptor new
2. ti after query
   - Expected: slow.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ti = TimingInterceptor.new(100)
ti.after_query("SELECT 1", 10, 1)
val slow = ti.slow_queries
expect(slow.len()).to_equal(0)
```

</details>

#### before_execute

#### is a no-op

1. ti before execute
   - Expected: ti.slow_queries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ti = TimingInterceptor.new(100)
ti.before_execute("SELECT 1")
# No exception, no state change
expect(ti.slow_queries.len()).to_equal(0)
```

</details>

#### before_query

#### is a no-op

1. ti before query
   - Expected: ti.slow_queries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ti = TimingInterceptor.new(100)
ti.before_query("SELECT 1")
expect(ti.slow_queries.len()).to_equal(0)
```

</details>

### LoggingInterceptor

#### before_execute

#### logs before execute

1. var li = LoggingInterceptor new
2. li before execute
   - Expected: log.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var li = LoggingInterceptor.new()
li.before_execute("INSERT INTO users VALUES (1, 'Alice')")
val log = li.get_log()
expect(log.len()).to_equal(1)
expect(log[0]).to_start_with("[EXEC]")
expect(log[0]).to_contain("INSERT INTO")
```

</details>

#### after_execute

#### logs after execute with duration and success

1. var li = LoggingInterceptor new
2. li after execute
   - Expected: log.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var li = LoggingInterceptor.new()
li.after_execute("UPDATE users SET name='Bob'", 5, true)
val log = li.get_log()
expect(log.len()).to_equal(1)
expect(log[0]).to_start_with("[EXEC DONE]")
expect(log[0]).to_contain("5ms")
expect(log[0]).to_contain("success=true")
```

</details>

#### logs failed execution

1. var li = LoggingInterceptor new
2. li after execute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var li = LoggingInterceptor.new()
li.after_execute("BAD SQL", 2, false)
val log = li.get_log()
expect(log[0]).to_contain("success=false")
```

</details>

#### before_query

#### logs before query

1. var li = LoggingInterceptor new
2. li before query
   - Expected: log.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var li = LoggingInterceptor.new()
li.before_query("SELECT * FROM users")
val log = li.get_log()
expect(log.len()).to_equal(1)
expect(log[0]).to_start_with("[QUERY]")
```

</details>

#### after_query

#### logs after query with duration and row count

1. var li = LoggingInterceptor new
2. li after query
   - Expected: log.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var li = LoggingInterceptor.new()
li.after_query("SELECT * FROM users", 10, 25)
val log = li.get_log()
expect(log.len()).to_equal(1)
expect(log[0]).to_start_with("[QUERY DONE]")
expect(log[0]).to_contain("10ms")
expect(log[0]).to_contain("25 rows")
```

</details>

#### full lifecycle

#### logs before and after execute in sequence

1. var li = LoggingInterceptor new
2. li before execute
3. li after execute
   - Expected: log.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var li = LoggingInterceptor.new()
li.before_execute("INSERT INTO t VALUES (1)")
li.after_execute("INSERT INTO t VALUES (1)", 3, true)
val log = li.get_log()
expect(log.len()).to_equal(2)
expect(log[0]).to_start_with("[EXEC]")
expect(log[1]).to_start_with("[EXEC DONE]")
```

</details>

#### logs before and after query in sequence

1. var li = LoggingInterceptor new
2. li before query
3. li after query
   - Expected: log.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var li = LoggingInterceptor.new()
li.before_query("SELECT 1")
li.after_query("SELECT 1", 1, 1)
val log = li.get_log()
expect(log.len()).to_equal(2)
expect(log[0]).to_start_with("[QUERY]")
expect(log[1]).to_start_with("[QUERY DONE]")
```

</details>

#### clear_log

#### clears all log entries

1. var li = LoggingInterceptor new
2. li before execute
3. li before execute
   - Expected: li.get_log().len() equals `2`
4. li clear log
   - Expected: li.get_log().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var li = LoggingInterceptor.new()
li.before_execute("sql1")
li.before_execute("sql2")
expect(li.get_log().len()).to_equal(2)
li.clear_log()
expect(li.get_log().len()).to_equal(0)
```

</details>

### RetryInterceptor

#### retry counting

#### starts with zero retry count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ri = RetryInterceptor.new(3, 100)
expect(ri.retry_count).to_equal(0)
```

</details>

#### increments retry count on failure

1. var ri = RetryInterceptor new
2. ri after execute
   - Expected: ri.retry_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ri = RetryInterceptor.new(3, 100)
ri.after_execute("SELECT 1", 10, false)
expect(ri.retry_count).to_equal(1)
```

</details>

#### does not increment on success

1. var ri = RetryInterceptor new
2. ri after execute
   - Expected: ri.retry_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ri = RetryInterceptor.new(3, 100)
ri.after_execute("SELECT 1", 10, true)
expect(ri.retry_count).to_equal(0)
```

</details>

#### counts multiple failures

1. var ri = RetryInterceptor new
2. ri after execute
3. ri after execute
4. ri after execute
   - Expected: ri.retry_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ri = RetryInterceptor.new(5, 100)
ri.after_execute("sql1", 1, false)
ri.after_execute("sql2", 1, false)
ri.after_execute("sql3", 1, false)
expect(ri.retry_count).to_equal(3)
```

</details>

#### counts mixed success and failure

1. var ri = RetryInterceptor new
2. ri after execute
3. ri after execute
4. ri after execute
5. ri after execute
   - Expected: ri.retry_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ri = RetryInterceptor.new(5, 100)
ri.after_execute("ok", 1, true)
ri.after_execute("fail", 1, false)
ri.after_execute("ok2", 1, true)
ri.after_execute("fail2", 1, false)
expect(ri.retry_count).to_equal(2)
```

</details>

#### configuration

#### stores max_retries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ri = RetryInterceptor.new(3, 200)
expect(ri.max_retries).to_equal(3)
```

</details>

#### stores delay_ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ri = RetryInterceptor.new(3, 200)
expect(ri.delay_ms).to_equal(200)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/sql/sql_interceptor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TimingInterceptor
- LoggingInterceptor
- RetryInterceptor

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
