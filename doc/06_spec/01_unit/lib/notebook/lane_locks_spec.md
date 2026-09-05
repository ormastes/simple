# lane_locks_spec

> Lane locks unit spec (Stream H, task H2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lane_locks_spec

Lane locks unit spec (Stream H, task H2).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/notebook/lane_locks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Lane locks unit spec (Stream H, task H2).

Covers exclusive-key contention between two notebook sessions ("blocked:
lane held by session <id>" wording, matching types.spl's LaneStatus), lock
release on explicit shutdown, and stale-lock takeover via a real pid
liveness check (rt_process_exists) — no fabricated aliveness booleans.

Design: doc/05_design/app/tools/notebook_lanes_architecture.md
Plan:   doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md (Stream H, H2)

## Scenarios

### Lane locks — exclusive key contention

#### grants the key to the first session

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- grants the key to the first session
   - Expected: diag equals ``
   - Expected: reg.holder("board-1") equals `session-a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("grants the key to the first session")
val reg = LaneLockRegistry.create()
val our_pid = rt_getpid()
val diag = reg.acquire("board-1", "session-a", our_pid)
expect(diag).to_equal("")
expect(reg.holder("board-1")).to_equal("session-a")
assert_true(reg.is_held("board-1"))
```

</details>

#### blocks a second session contending for the same key while the holder is alive

- blocks a second session contending for the same key while the holder is alive
   - Expected: first equals ``
   - Expected: second equals `blocked: lane held by session session-a`
   - Expected: reg.holder("board-1") equals `session-a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blocks a second session contending for the same key while the holder is alive")
val reg = LaneLockRegistry.create()
val our_pid = rt_getpid()
val first = reg.acquire("board-1", "session-a", our_pid)
expect(first).to_equal("")
val second = reg.acquire("board-1", "session-b", our_pid)
expect(second).to_equal("blocked: lane held by session session-a")
# The original holder is unaffected by the failed contender.
expect(reg.holder("board-1")).to_equal("session-a")
```

</details>

#### is idempotent for the session that already holds the key

- is idempotent for the session that already holds the key
   - Expected: first equals ``
   - Expected: reacquire equals ``
   - Expected: reg.holder("board-1") equals `session-a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is idempotent for the session that already holds the key")
val reg = LaneLockRegistry.create()
val our_pid = rt_getpid()
val first = reg.acquire("board-1", "session-a", our_pid)
expect(first).to_equal("")
val reacquire = reg.acquire("board-1", "session-a", our_pid)
expect(reacquire).to_equal("")
expect(reg.holder("board-1")).to_equal("session-a")
```

</details>

#### does not cross-contend on different keys

- does not cross-contend on different keys
   - Expected: a equals ``
   - Expected: b equals ``
   - Expected: reg.holder("board-1") equals `session-a`
   - Expected: reg.holder("board-2") equals `session-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not cross-contend on different keys")
val reg = LaneLockRegistry.create()
val our_pid = rt_getpid()
val a = reg.acquire("board-1", "session-a", our_pid)
val b = reg.acquire("board-2", "session-b", our_pid)
expect(a).to_equal("")
expect(b).to_equal("")
expect(reg.holder("board-1")).to_equal("session-a")
expect(reg.holder("board-2")).to_equal("session-b")
```

</details>

### Lane locks — release on explicit shutdown

#### releases the key so a contending session can acquire it

- releases the key so a contending session can acquire it
   - Expected: second equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("releases the key so a contending session can acquire it")
val reg = LaneLockRegistry.create()
val our_pid = rt_getpid()
val _acquired = reg.acquire("board-1", "session-a", our_pid)
val released = reg.release("board-1", "session-a")
assert_true(released)
assert_false(reg.is_held("board-1"))
val second = reg.acquire("board-1", "session-b", our_pid)
expect(second).to_equal("")
```

</details>

#### refuses to release a key held by a different session

- refuses to release a key held by a different session
   - Expected: reg.holder("board-1") equals `session-a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses to release a key held by a different session")
val reg = LaneLockRegistry.create()
val our_pid = rt_getpid()
val _acquired = reg.acquire("board-1", "session-a", our_pid)
val released = reg.release("board-1", "session-b")
assert_false(released)
expect(reg.holder("board-1")).to_equal("session-a")
```

</details>

#### is a no-op releasing an unheld key

- is a no-op releasing an unheld key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is a no-op releasing an unheld key")
val reg = LaneLockRegistry.create()
val released = reg.release("board-1", "session-a")
assert_false(released)
```

</details>

#### release_all_for_session sweeps every key that session holds

- release_all_for_session sweeps every key that session holds
   - Expected: count equals `2`
   - Expected: reg.holder("board-3") equals `session-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("release_all_for_session sweeps every key that session holds")
val reg = LaneLockRegistry.create()
val our_pid = rt_getpid()
val _a = reg.acquire("board-1", "session-a", our_pid)
val _b = reg.acquire("board-2", "session-a", our_pid)
val _c = reg.acquire("board-3", "session-b", our_pid)
val count = reg.release_all_for_session("session-a")
expect(count).to_equal(2)
assert_false(reg.is_held("board-1"))
assert_false(reg.is_held("board-2"))
# session-b's lock is untouched by session-a's shutdown sweep.
expect(reg.holder("board-3")).to_equal("session-b")
```

</details>

### Lane locks — stale-lock takeover via real pid liveness check

#### reclaims a key whose holder pid is dead instead of blocking

- reclaims a key whose holder pid is dead instead of blocking
   - Expected: stale equals ``
   - Expected: takeover equals ``
   - Expected: reg.holder("board-1") equals `session-b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reclaims a key whose holder pid is dead instead of blocking")
val reg = LaneLockRegistry.create()
val stale = reg.acquire("board-1", "session-a", DEAD_PID)
expect(stale).to_equal("")
val our_pid = rt_getpid()
val takeover = reg.acquire("board-1", "session-b", our_pid)
expect(takeover).to_equal("")
expect(reg.holder("board-1")).to_equal("session-b")
```

</details>

#### is_held reports false once the holder pid is dead

- is_held reports false once the holder pid is dead


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_held reports false once the holder pid is dead")
val reg = LaneLockRegistry.create()
val _acquired = reg.acquire("board-1", "session-a", DEAD_PID)
assert_false(reg.is_held("board-1"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `187c44713f4192e1a677c2c062380221ccc17a418b17852a637c08a9ef60d5ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `187c44713f4192e1a677c2c062380221ccc17a418b17852a637c08a9ef60d5ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `187c44713f4192e1a677c2c062380221ccc17a418b17852a637c08a9ef60d5ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/notebook/lane_locks_spec.spl
mirror: doc/06_spec/01_unit/lib/notebook/lane_locks_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/notebook/lane_locks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/notebook/lane_locks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/notebook/lane_locks_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/notebook/lane_locks_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'grants the key to the first session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/notebook/lane_locks_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks a second session contending for the same key while the holder is alive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/notebook/lane_locks_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is idempotent for the session that already holds the key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
