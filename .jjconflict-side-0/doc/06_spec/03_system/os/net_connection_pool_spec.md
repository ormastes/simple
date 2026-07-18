# Net Connection Pool Specification

> <details>

<!-- sdn-diagram:id=net_connection_pool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_connection_pool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_connection_pool_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_connection_pool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Connection Pool Specification

## Scenarios

### FR-NET-0013 TCP connection pool

#### host-keyed reuse

#### releases and reacquires a matching non-expired idle fd

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = pool_config_new(2u32, 1000u64, 50u64)
val empty = connection_pool_new(config)
val released = pool_release(empty, pooled_connection_new(7, "example.test", 443u16, 10u64), 20u64)
val acquired = pool_acquire(released, "example.test", 443u16, 100u64)
expect(acquired[1].found).to_equal(true)
expect(acquired[1].reused).to_equal(true)
expect(acquired[1].fd).to_equal(7)
expect(pool_stats(acquired[0]).idle_count).to_equal(0u64)
```

</details>

#### misses expired entries and keeps the acquire counter accurate

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = pool_config_new(2u32, 25u64, 50u64)
val empty = connection_pool_new(config)
val released = pool_release(empty, pooled_connection_new(8, "example.test", 443u16, 10u64), 10u64)
val acquired = pool_acquire(released, "example.test", 443u16, 100u64)
expect(acquired[1].found).to_equal(false)
expect(acquired[0].total_acquired).to_equal(1u64)
expect(pool_stats(acquired[0]).idle_count).to_equal(1u64)
```

</details>

#### capacity and eviction

#### evicts the oldest idle fd for a host when release reaches capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = pool_config_new(2u32, 1000u64, 50u64)
val p0 = connection_pool_new(config)
val p1 = pool_release(p0, pooled_connection_new(1, "example.test", 80u16, 10u64), 10u64)
val p2 = pool_release(p1, pooled_connection_new(2, "example.test", 80u16, 20u64), 20u64)
val p3 = pool_release(p2, pooled_connection_new(3, "example.test", 80u16, 30u64), 30u64)
expect(p3.total_evicted).to_equal(1u64)
expect(pool_stats(p3).idle_count).to_equal(2u64)
val miss_oldest = pool_acquire(p3, "example.test", 80u16, 40u64)
expect(miss_oldest[1].fd).to_equal(2)
```

</details>

#### removes expired connections and reports stable summary text

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = pool_config_new(4u32, 25u64, 50u64)
val p0 = connection_pool_new(config)
val p1 = pool_release(p0, pooled_connection_new(1, "a.test", 80u16, 10u64), 10u64)
val p2 = pool_release(p1, pooled_connection_new(2, "b.test", 80u16, 90u64), 90u64)
val evicted = pool_evict_expired(p2, 100u64)
val stats = pool_stats(evicted[0])
expect(evicted[1]).to_equal(1u64)
expect(stats.idle_count).to_equal(1u64)
expect(pool_host_key("b.test", 80u16)).to_equal("b.test:80")
expect(pool_stats_summary(stats)).to_contain("idle=1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/net_connection_pool_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FR-NET-0013 TCP connection pool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
