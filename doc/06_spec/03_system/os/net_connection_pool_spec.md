# Net Connection Pool Specification

> Tests covering FR-NET-0013 TCP connection pool.

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

- releases and reacquires a matching non-expired idle fd
   - Expected: acquired[1].found is true
   - Expected: acquired[1].reused is true
   - Expected: acquired[1].fd equals `7`
   - Expected: pool_stats(acquired[0]).idle_count equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("releases and reacquires a matching non-expired idle fd")
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

- misses expired entries and keeps the acquire counter accurate
   - Expected: acquired[1].found is false
   - Expected: acquired[0].total_acquired equals `1u64`
   - Expected: pool_stats(acquired[0]).idle_count equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("misses expired entries and keeps the acquire counter accurate")
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

- evicts the oldest idle fd for a host when release reaches capacity
   - Expected: p3.total_evicted equals `1u64`
   - Expected: pool_stats(p3).idle_count equals `2u64`
   - Expected: miss_oldest[1].fd equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("evicts the oldest idle fd for a host when release reaches capacity")
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

- removes expired connections and reports stable summary text
   - Expected: evicted[1] equals `1u64`
   - Expected: stats.idle_count equals `1u64`
   - Expected: pool_host_key("b.test", 80u16) equals `b.test:80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("removes expired connections and reports stable summary text")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FR-NET-0013 TCP connection pool.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b1ea567e5feee02768c055c5fa7ee674de3693d68db79ec5cd27f3e2a1d1a945`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1ea567e5feee02768c055c5fa7ee674de3693d68db79ec5cd27f3e2a1d1a945`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1ea567e5feee02768c055c5fa7ee674de3693d68db79ec5cd27f3e2a1d1a945`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/os/net_connection_pool_spec.spl
mirror: doc/06_spec/03_system/os/net_connection_pool_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/net_connection_pool_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/net_connection_pool_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/net_connection_pool_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/net_connection_pool_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'releases and reacquires a matching non-expired idle fd' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_connection_pool_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'misses expired entries and keeps the acquire counter accurate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/net_connection_pool_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evicts the oldest idle fd for a host when release reaches capacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
