# Test Daemon Agent Pool Specification

> <details>

<!-- sdn-diagram:id=test_daemon_agent_pool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_agent_pool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_agent_pool_spec -> std
test_daemon_agent_pool_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_agent_pool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Daemon Agent Pool Specification

## Scenarios

### AgentPool

#### registers agents

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(2)
expect(pool.register_agent("agent-1", "linux")).to_equal(true)
expect(pool.register_agent("agent-2", "mac")).to_equal(true)
expect(pool.active_agent_count()).to_equal(2)
```

</details>

#### claims batches only for registered agents

1. pool load pending tests
   - Expected: pool.claim_batch("missing").len() equals `0`
2. pool register agent
   - Expected: batch.len() equals `2`
   - Expected: pool.pending_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(2)
pool.load_pending_tests(["test/a.spl", "test/b.spl", "test/c.spl"])
expect(pool.claim_batch("missing").len()).to_equal(0)

pool.register_agent("agent-1", "linux")
val batch = pool.claim_batch("agent-1")
expect(batch.len()).to_equal(2)
expect(pool.pending_count()).to_equal(1)
```

</details>

#### does not double-assign completed or in-progress tests when loading pending

1. pool register agent
2. pool load pending tests
   - Expected: batch.len() equals `2`
3. pool load pending tests
   - Expected: pool.pending_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(5)
pool.register_agent("agent-1", "linux")
pool.load_pending_tests(["test/a.spl", "test/b.spl"])
val batch = pool.claim_batch("agent-1")
expect(batch.len()).to_equal(2)

pool.load_pending_tests(["test/a.spl", "test/b.spl", "test/c.spl"])
expect(pool.pending_count()).to_equal(1)
```

</details>

#### records results and updates counts

1. pool register agent
2. pool load pending tests
3. pool claim batch
   - Expected: pool.report_result("agent-1", "test/a.spl", 2, 1, 0, 10, "ok") is true
   - Expected: pool.completed_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(5)
pool.register_agent("agent-1", "linux")
pool.load_pending_tests(["test/a.spl"])
pool.claim_batch("agent-1")

expect(pool.report_result("agent-1", "test/a.spl", 2, 1, 0, 10, "ok")).to_equal(true)
expect(pool.completed_count()).to_equal(1)
```

</details>

#### returns in-progress work to pending on deregister

1. pool register agent
2. pool load pending tests
   - Expected: batch.len() equals `2`
   - Expected: pool.deregister_agent("agent-1") is true
   - Expected: pool.active_agent_count() equals `0`
   - Expected: pool.pending_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = agent_pool_new(5)
pool.register_agent("agent-1", "linux")
pool.load_pending_tests(["test/a.spl", "test/b.spl"])
val batch = pool.claim_batch("agent-1")
expect(batch.len()).to_equal(2)

expect(pool.deregister_agent("agent-1")).to_equal(true)
expect(pool.active_agent_count()).to_equal(0)
expect(pool.pending_count()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_agent_pool_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AgentPool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
