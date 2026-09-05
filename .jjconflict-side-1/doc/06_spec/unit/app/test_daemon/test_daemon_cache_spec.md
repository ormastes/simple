# test_daemon_cache_spec

> Purpose: Prove that TestResultCache.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_cache_spec

Purpose: Prove that TestResultCache.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_daemon/test_daemon_cache_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that TestResultCache.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### TestResultCache

### recording results

#### stores test result

- stores test result
- Verify: stores test result
   - Expected: cache_count() equals `1`
   - Expected: cache_get_status("test/foo_spec.spl") equals `2`
   - Expected: cache_get_passed("test/foo_spec.spl") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores test result")
step("Verify: stores test result")
# @req: REQ-APP-TEST-DAEMON-001
cache_reset()
cache_record("test/foo_spec.spl", 12345, 2, 10, 0, 500)
expect(cache_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(cache_get_status("test/foo_spec.spl")).to_equal(2)
expect(cache_get_passed("test/foo_spec.spl")).to_equal(10)
```

</details>

#### stores multiple results

- stores multiple results
- Verify: stores multiple results
   - Expected: cache_count() equals `2`
   - Expected: cache_get_passed("test/a_spec.spl") equals `5`
   - Expected: cache_get_failed("test/b_spec.spl") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores multiple results")
step("Verify: stores multiple results")
cache_reset()
cache_record("test/a_spec.spl", 111, 2, 5, 0, 200)
cache_record("test/b_spec.spl", 222, 3, 3, 2, 800)
expect(cache_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(cache_get_passed("test/a_spec.spl")).to_equal(5)
expect(cache_get_failed("test/b_spec.spl")).to_equal(2)
```

</details>

#### updates existing entry

- updates existing entry
- Verify: updates existing entry
   - Expected: cache_count() equals `1`
   - Expected: cache_get_status("test/x_spec.spl") equals `2`
   - Expected: cache_get_passed("test/x_spec.spl") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("updates existing entry")
step("Verify: updates existing entry")
cache_reset()
cache_record("test/x_spec.spl", 100, 3, 0, 1, 100)
cache_record("test/x_spec.spl", 200, 2, 5, 0, 300)
expect(cache_count()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(cache_get_status("test/x_spec.spl")).to_equal(2)
expect(cache_get_passed("test/x_spec.spl")).to_equal(5)
```

</details>

### freshness checking

#### returns fresh when hash matches

- returns fresh when hash matches
- Verify: returns fresh when hash matches
   - Expected: cache_check_freshness("test/foo_spec.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns fresh when hash matches")
step("Verify: returns fresh when hash matches")
cache_reset()
src_set_hash("test/foo_spec.spl", 12345)
cache_record("test/foo_spec.spl", 12345, 2, 10, 0, 500)
expect(cache_check_freshness("test/foo_spec.spl")).to_equal(true)
```

</details>

#### returns stale when hash differs

- returns stale when hash differs
- Verify: returns stale when hash differs
   - Expected: cache_check_freshness("test/foo_spec.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns stale when hash differs")
step("Verify: returns stale when hash differs")
cache_reset()
src_set_hash("test/foo_spec.spl", 99999)
cache_record("test/foo_spec.spl", 12345, 2, 10, 0, 500)
expect(cache_check_freshness("test/foo_spec.spl")).to_equal(false)
```

</details>

#### returns stale for uncached test

- returns stale for uncached test
- Verify: returns stale for uncached test
   - Expected: cache_check_freshness("test/new_spec.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns stale for uncached test")
step("Verify: returns stale for uncached test")
cache_reset()
src_set_hash("test/new_spec.spl", 11111)
expect(cache_check_freshness("test/new_spec.spl")).to_equal(false)
```

</details>

#### returns stale when no source hash

- returns stale when no source hash
- Verify: returns stale when no source hash
   - Expected: cache_check_freshness("test/foo_spec.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns stale when no source hash")
step("Verify: returns stale when no source hash")
cache_reset()
cache_record("test/foo_spec.spl", 12345, 2, 10, 0, 500)
expect(cache_check_freshness("test/foo_spec.spl")).to_equal(false)
```

</details>

### invalidation

#### clears all entries

- clears all entries
- Verify: clears all entries
   - Expected: cache_count() equals `2`
   - Expected: cache_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all entries")
step("Verify: clears all entries")
cache_reset()
cache_record("test/a_spec.spl", 111, 2, 5, 0, 200)
cache_record("test/b_spec.spl", 222, 2, 3, 0, 100)
expect(cache_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
cache_invalidate_all()
expect(cache_count()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### freshness returns stale after invalidation

- freshness returns stale after invalidation
- Verify: freshness returns stale after invalidation
   - Expected: cache_check_freshness("test/foo_spec.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("freshness returns stale after invalidation")
step("Verify: freshness returns stale after invalidation")
cache_reset()
src_set_hash("test/foo_spec.spl", 12345)
cache_record("test/foo_spec.spl", 12345, 2, 10, 0, 500)
cache_invalidate_all()
expect(cache_check_freshness("test/foo_spec.spl")).to_equal(false)
```

</details>

### duration tracking

#### records test duration

- records test duration
- Verify: records test duration
   - Expected: cache_get_duration("test/slow_spec.spl") equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records test duration")
step("Verify: records test duration")
cache_reset()
cache_record("test/slow_spec.spl", 100, 2, 1, 0, 5000)
expect(cache_get_duration("test/slow_spec.spl")).to_equal(5000)
```

</details>

#### returns 0 for unknown test

- returns 0 for unknown test
- Verify: returns 0 for unknown test
   - Expected: cache_get_duration("test/unknown_spec.spl") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for unknown test")
step("Verify: returns 0 for unknown test")
cache_reset()
expect(cache_get_duration("test/unknown_spec.spl")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-TEST-DAEMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5498179f11ef556c787ed641cb7d0ac91f6000662f43742f899d09b3f6885cf2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5498179f11ef556c787ed641cb7d0ac91f6000662f43742f899d09b3f6885cf2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5498179f11ef556c787ed641cb7d0ac91f6000662f43742f899d09b3f6885cf2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/test_daemon/test_daemon_cache_spec.spl
mirror: doc/06_spec/unit/app/test_daemon/test_daemon_cache_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_daemon/test_daemon_cache_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_daemon/test_daemon_cache_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_daemon/test_daemon_cache_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/test_daemon/test_daemon_cache_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores test result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_daemon/test_daemon_cache_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores multiple results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_daemon/test_daemon_cache_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'updates existing entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
