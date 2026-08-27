# daemon_sdk_lock_spec

> Purpose: Prove that DaemonLock.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# daemon_sdk_lock_spec

Purpose: Prove that DaemonLock.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/daemon_sdk/daemon_sdk_lock_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that DaemonLock.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### DaemonLock

### acquisition

#### acquires lock when none exists

- acquires lock when none exists
- Verify: acquires lock when none exists
   - Expected: pid equals `12345`
   - Expected: lk_exists(".build/test.lock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("acquires lock when none exists")
step("Verify: acquires lock when none exists")
# @req: REQ-LIB-DAEMON-SDK-001
lk_reset()
val pid = mock_try_acquire(".build/test.lock")
expect(pid).to_equal(12345)  # oracle: 12345 — named expected value from the requirement
expect(lk_exists(".build/test.lock")).to_equal(true)
```

</details>

#### fails when another daemon holds lock

- fails when another daemon holds lock
- Verify: fails when another daemon holds lock
   - Expected: pid equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when another daemon holds lock")
step("Verify: fails when another daemon holds lock")
lk_reset()
lk_write(".build/test.lock", 99999)
lk_add_alive(99999)
val pid = mock_try_acquire(".build/test.lock")
expect(pid).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

#### takes over stale lock

- takes over stale lock
- Verify: takes over stale lock
   - Expected: pid equals `12345`
   - Expected: lk_read_pid(".build/test.lock") equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("takes over stale lock")
step("Verify: takes over stale lock")
lk_reset()
lk_write(".build/test.lock", 99999)
# 99999 is NOT in alive list → stale
val pid = mock_try_acquire(".build/test.lock")
expect(pid).to_equal(12345)  # oracle: 12345 — named expected value from the requirement
expect(lk_read_pid(".build/test.lock")).to_equal(12345)
```

</details>

#### handles multiple lock paths independently

- handles multiple lock paths independently
- Verify: handles multiple lock paths independently
   - Expected: p1 equals `12345`
   - Expected: p2 equals `12345`
   - Expected: lk_lock_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple lock paths independently")
step("Verify: handles multiple lock paths independently")
lk_reset()
val p1 = mock_try_acquire(".build/daemon_a.lock")
val p2 = mock_try_acquire(".build/daemon_b.lock")
expect(p1).to_equal(12345)  # oracle: 12345 — named expected value from the requirement
expect(p2).to_equal(12345)  # oracle: 12345 — named expected value from the requirement
expect(lk_lock_count()).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

### release

#### releases owned lock

- releases owned lock
- Verify: releases owned lock
   - Expected: ok is true
   - Expected: lk_exists(".build/test.lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("releases owned lock")
step("Verify: releases owned lock")
lk_reset()
mock_try_acquire(".build/test.lock")
val ok = mock_release(12345, ".build/test.lock")
expect(ok).to_equal(true)
expect(lk_exists(".build/test.lock")).to_equal(false)
```

</details>

#### refuses to release lock owned by another

- refuses to release lock owned by another
- Verify: refuses to release lock owned by another
   - Expected: ok is false
   - Expected: lk_exists(".build/test.lock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to release lock owned by another")
step("Verify: refuses to release lock owned by another")
lk_reset()
lk_write(".build/test.lock", 99999)
val ok = mock_release(12345, ".build/test.lock")
expect(ok).to_equal(false)
expect(lk_exists(".build/test.lock")).to_equal(true)
```

</details>

#### succeeds when lock does not exist

- succeeds when lock does not exist
- Verify: succeeds when lock does not exist
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("succeeds when lock does not exist")
step("Verify: succeeds when lock does not exist")
lk_reset()
val ok = mock_release(12345, ".build/nonexistent.lock")
expect(ok).to_equal(true)
```

</details>

### is_running

#### returns false when no lock

- returns false when no lock
- Verify: returns false when no lock
   - Expected: mock_is_running(".build/test.lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when no lock")
step("Verify: returns false when no lock")
lk_reset()
expect(mock_is_running(".build/test.lock")).to_equal(false)
```

</details>

#### returns true when lock held by alive process

- returns true when lock held by alive process
- Verify: returns true when lock held by alive process
   - Expected: mock_is_running(".build/test.lock") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true when lock held by alive process")
step("Verify: returns true when lock held by alive process")
lk_reset()
lk_write(".build/test.lock", 12345)
expect(mock_is_running(".build/test.lock")).to_equal(true)
```

</details>

#### returns false when lock held by dead process

- returns false when lock held by dead process
- Verify: returns false when lock held by dead process
   - Expected: mock_is_running(".build/test.lock") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when lock held by dead process")
step("Verify: returns false when lock held by dead process")
lk_reset()
lk_write(".build/test.lock", 99999)
expect(mock_is_running(".build/test.lock")).to_equal(false)
```

</details>

### stale lock recovery

#### replaces stale lock and acquires

- replaces stale lock and acquires
- Verify: replaces stale lock and acquires
   - Expected: pid equals `12345`
   - Expected: lk_read_pid(".build/test.lock") equals `12345`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces stale lock and acquires")
step("Verify: replaces stale lock and acquires")
lk_reset()
lk_write(".build/test.lock", 88888)
# 88888 not alive
val pid = mock_try_acquire(".build/test.lock")
expect(pid).to_equal(12345)  # oracle: 12345 — named expected value from the requirement
expect(lk_read_pid(".build/test.lock")).to_equal(12345)
```

</details>

#### does not replace active lock

- does not replace active lock
- Verify: does not replace active lock
   - Expected: pid equals `-1`
   - Expected: lk_read_pid(".build/test.lock") equals `77777`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not replace active lock")
step("Verify: does not replace active lock")
lk_reset()
lk_write(".build/test.lock", 77777)
lk_add_alive(77777)
val pid = mock_try_acquire(".build/test.lock")
expect(pid).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect(lk_read_pid(".build/test.lock")).to_equal(77777)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-DAEMON-SDK-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `925cf18128dd5d8d6ccda61223560c280689fc00b8be754ea1fac077d3336394`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `925cf18128dd5d8d6ccda61223560c280689fc00b8be754ea1fac077d3336394`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `925cf18128dd5d8d6ccda61223560c280689fc00b8be754ea1fac077d3336394`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/daemon_sdk/daemon_sdk_lock_spec.spl
mirror: doc/06_spec/unit/lib/daemon_sdk/daemon_sdk_lock_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/daemon_sdk/daemon_sdk_lock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/daemon_sdk/daemon_sdk_lock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/daemon_sdk/daemon_sdk_lock_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/daemon_sdk/daemon_sdk_lock_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'acquires lock when none exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/daemon_sdk/daemon_sdk_lock_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails when another daemon holds lock' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/daemon_sdk/daemon_sdk_lock_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'takes over stale lock' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
