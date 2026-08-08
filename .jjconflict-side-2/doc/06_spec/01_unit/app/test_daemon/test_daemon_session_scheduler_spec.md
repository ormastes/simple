# test_daemon_session_scheduler_spec

> @cover src/app/test_daemon/session_scheduler.spl 80%

<!-- sdn-diagram:id=test_daemon_session_scheduler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_session_scheduler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_session_scheduler_spec -> std
test_daemon_session_scheduler_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_session_scheduler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_session_scheduler_spec

@cover src/app/test_daemon/session_scheduler.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-SCH-001 to #TDMN-SCH-030 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_session_scheduler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/app/test_daemon/session_scheduler.spl 80%
@cover src/app/test_daemon/session_types.spl 60%
@cover src/app/test_daemon/session_broker.spl 60%

Test Daemon Session Scheduler Specification

Tests the session scheduler that groups and prioritizes session-capable tests.
Verifies schedule grouping, priority ordering, flattening, and queries.

## Scenarios

### Session Scheduler Priority Calculation

#### assigns priority 0 to shared_read_only (#TDMN-SCH-001)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = reuse_priority(REUSE_SHARED_READ_ONLY)
expect(p).to_equal(0)
```

</details>

#### assigns priority 1 to shared_with_snapshot (#TDMN-SCH-002)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = reuse_priority(REUSE_SHARED_WITH_SNAPSHOT)
expect(p).to_equal(1)
```

</details>

#### assigns priority 2 to shared_with_reset (#TDMN-SCH-003)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = reuse_priority(REUSE_SHARED_WITH_RESET)
expect(p).to_equal(2)
```

</details>

#### assigns priority 3 to exclusive_reused (#TDMN-SCH-004)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = reuse_priority(REUSE_EXCLUSIVE_REUSED)
expect(p).to_equal(3)
```

</details>

#### assigns priority 4 to fresh_per_test (#TDMN-SCH-005)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = reuse_priority(REUSE_FRESH_PER_TEST)
expect(p).to_equal(4)
```

</details>

#### assigns priority 5 to unknown reuse mode (#TDMN-SCH-006)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = reuse_priority(99)
expect(p).to_equal(5)
```

</details>

### Session Scheduler Empty and Single Entry

#### produces empty schedule from empty input (#TDMN-SCH-007)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var metas: [TestSessionMeta] = []
val schedule = schedule_session_tests(metas)
expect(schedule.total_tests).to_equal(0)
expect(schedule.total_groups).to_equal(0)
expect(schedule.total_ungrouped).to_equal(0)
```

</details>

#### puts a local test into ungrouped (#TDMN-SCH-008)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = test_session_meta_default("test/specs/basic_spec.spl")
var metas: [TestSessionMeta] = [meta]
val schedule = schedule_session_tests(metas)
expect(schedule.total_tests).to_equal(1)
expect(schedule.total_groups).to_equal(0)
expect(schedule.total_ungrouped).to_equal(1)
```

</details>

#### puts a QEMU test into a group (#TDMN-SCH-009)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta = _make_qemu_meta("test/system/qemu/boot_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
var metas: [TestSessionMeta] = [meta]
val schedule = schedule_session_tests(metas)
expect(schedule.total_tests).to_equal(1)
expect(schedule.total_groups).to_equal(1)
expect(schedule.total_ungrouped).to_equal(0)
```

</details>

### Session Scheduler Grouping

#### groups two QEMU tests with same target into one group (#TDMN-SCH-010)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta1 = _make_qemu_meta("test/system/qemu/a_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
val meta2 = _make_qemu_meta("test/system/qemu/b_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
var metas: [TestSessionMeta] = [meta1, meta2]
val schedule = schedule_session_tests(metas)
expect(schedule.total_groups).to_equal(1)
val session_count = schedule_total_session_tests(schedule)
expect(session_count).to_equal(2)
```

</details>

#### keeps separate QEMU tests in one warm shared session without reset (#TDMN-SCH-010B)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta1 = _make_qemu_meta("test/system/qemu/a_spec.spl", "riscv64", REUSE_SHARED_READ_ONLY)
val meta2 = _make_qemu_meta("test/system/qemu/b_spec.spl", "riscv64", REUSE_SHARED_READ_ONLY)
var metas: [TestSessionMeta] = [meta1, meta2]
val schedule = schedule_session_tests(metas)
expect(schedule.total_groups).to_equal(1)
expect(schedule.groups[0].entries.len()).to_equal(2)
expect(schedule.groups[0].entries[0].file_path).to_equal("test/system/qemu/a_spec.spl")
expect(schedule.groups[0].entries[1].file_path).to_equal("test/system/qemu/b_spec.spl")
expect(schedule.groups[0].key.reuse_mode).to_equal(REUSE_SHARED_READ_ONLY)
expect(schedule.groups[0].key.reset_policy).to_equal(RESET_NONE)
```

</details>

#### separates QEMU tests with different targets (#TDMN-SCH-011)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta1 = _make_qemu_meta("test/system/qemu/a_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
val meta2 = _make_qemu_meta("test/system/qemu/b_spec.spl", "arm32", REUSE_SHARED_READ_ONLY)
var metas: [TestSessionMeta] = [meta1, meta2]
val schedule = schedule_session_tests(metas)
expect(schedule.total_groups).to_equal(2)
```

</details>

#### separates tests with different reuse modes even if same target (#TDMN-SCH-012)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta1 = _make_qemu_meta("test/system/qemu/a_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
val meta2 = _make_qemu_meta("test/system/qemu/b_spec.spl", "riscv32", REUSE_FRESH_PER_TEST)
var metas: [TestSessionMeta] = [meta1, meta2]
val schedule = schedule_session_tests(metas)
expect(schedule.total_groups).to_equal(2)
```

</details>

#### groups container tests separately from QEMU tests (#TDMN-SCH-013)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qemu = _make_qemu_meta("test/system/qemu/a_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
val container = _make_container_meta("test/container/b_spec.spl", "simple-test:latest")
var metas: [TestSessionMeta] = [qemu, container]
val schedule = schedule_session_tests(metas)
expect(schedule.total_groups).to_equal(2)
```

</details>

#### separates local and session tests correctly (#TDMN-SCH-014)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val local1 = test_session_meta_default("test/unit/basic_spec.spl")
val local2 = test_session_meta_default("test/unit/other_spec.spl")
val qemu = _make_qemu_meta("test/system/qemu/boot_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
var metas: [TestSessionMeta] = [local1, qemu, local2]
val schedule = schedule_session_tests(metas)
expect(schedule.total_groups).to_equal(1)
expect(schedule.total_ungrouped).to_equal(2)
```

</details>

### Session Scheduler Priority Ordering

#### orders read-only groups before fresh-per-test groups (#TDMN-SCH-015)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fresh = _make_qemu_meta("test/system/qemu/fresh_spec.spl", "x86_64", REUSE_FRESH_PER_TEST)
val readonly = _make_qemu_meta("test/system/qemu/readonly_spec.spl", "arm32", REUSE_SHARED_READ_ONLY)
# Insert fresh first, but scheduler should reorder
var metas: [TestSessionMeta] = [fresh, readonly]
val schedule = schedule_session_tests(metas)
expect(schedule.total_groups).to_equal(2)
val groups = schedule.groups
val first_priority = groups[0].priority
val second_priority = groups[1].priority
expect(first_priority).to_be_less_than(second_priority)
```

</details>

#### orders snapshot groups before reset groups (#TDMN-SCH-016)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = _make_qemu_meta("test/system/qemu/reset_spec.spl", "mips", REUSE_SHARED_WITH_RESET)
val snapshot = _make_qemu_meta("test/system/qemu/snap_spec.spl", "aarch64", REUSE_SHARED_WITH_SNAPSHOT)
var metas: [TestSessionMeta] = [reset, snapshot]
val schedule = schedule_session_tests(metas)
val groups = schedule.groups
expect(groups[0].priority).to_be_less_than(groups[1].priority)
```

</details>

#### maintains stable order for equal priorities (#TDMN-SCH-017)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val meta1 = _make_qemu_meta("test/system/qemu/a_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
val meta2 = _make_qemu_meta("test/system/qemu/b_spec.spl", "arm32", REUSE_SHARED_READ_ONLY)
var metas: [TestSessionMeta] = [meta1, meta2]
val schedule = schedule_session_tests(metas)
val groups = schedule.groups
# Both have same priority; first inserted should remain first
expect(groups[0].priority).to_equal(groups[1].priority)
```

</details>

### Session Scheduler Flatten and Queries

#### flattens session groups before ungrouped (#TDMN-SCH-018)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val local = test_session_meta_default("test/unit/local_spec.spl")
val qemu = _make_qemu_meta("test/system/qemu/boot_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
var metas: [TestSessionMeta] = [local, qemu]
val schedule = schedule_session_tests(metas)
val flat = schedule_flatten(schedule)
expect(flat.len()).to_equal(2)
# Session tests come first
expect(flat[0]).to_equal("test/system/qemu/boot_spec.spl")
expect(flat[1]).to_equal("test/unit/local_spec.spl")
```

</details>

#### returns only session file paths (#TDMN-SCH-019)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val local = test_session_meta_default("test/unit/local_spec.spl")
val qemu = _make_qemu_meta("test/system/qemu/boot_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
var metas: [TestSessionMeta] = [local, qemu]
val schedule = schedule_session_tests(metas)
val paths = schedule_session_file_paths(schedule)
expect(paths.len()).to_equal(1)
expect(paths[0]).to_equal("test/system/qemu/boot_spec.spl")
```

</details>

#### returns only local file paths (#TDMN-SCH-020)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val local = test_session_meta_default("test/unit/local_spec.spl")
val qemu = _make_qemu_meta("test/system/qemu/boot_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
var metas: [TestSessionMeta] = [local, qemu]
val schedule = schedule_session_tests(metas)
val paths = schedule_local_file_paths(schedule)
expect(paths.len()).to_equal(1)
expect(paths[0]).to_equal("test/unit/local_spec.spl")
```

</details>

#### counts total session tests across groups (#TDMN-SCH-021)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q1 = _make_qemu_meta("test/system/qemu/a_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
val q2 = _make_qemu_meta("test/system/qemu/b_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
val c1 = _make_container_meta("test/container/c_spec.spl", "simple-test:latest")
var metas: [TestSessionMeta] = [q1, q2, c1]
val schedule = schedule_session_tests(metas)
val total = schedule_total_session_tests(schedule)
expect(total).to_equal(3)
```

</details>

#### finds groups by kind (#TDMN-SCH-022)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q1 = _make_qemu_meta("test/system/qemu/a_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
val c1 = _make_container_meta("test/container/c_spec.spl", "simple-test:latest")
var metas: [TestSessionMeta] = [q1, c1]
val schedule = schedule_session_tests(metas)
val qemu_groups = schedule_group_for_kind(schedule, SESSION_KIND_QEMU_VM)
val container_groups = schedule_group_for_kind(schedule, SESSION_KIND_CONTAINER)
expect(qemu_groups.len()).to_equal(1)
expect(container_groups.len()).to_equal(1)
```

</details>

#### returns empty for nonexistent group id (#TDMN-SCH-023)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q1 = _make_qemu_meta("test/system/qemu/a_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
var metas: [TestSessionMeta] = [q1]
val schedule = schedule_session_tests(metas)
val entries = schedule_group_by_id(schedule, "nonexistent_group_id")
expect(entries.len()).to_equal(0)
```

</details>

### Session Scheduler Summary and Mixed

#### produces a non-empty summary (#TDMN-SCH-024)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q1 = _make_qemu_meta("test/system/qemu/a_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
var metas: [TestSessionMeta] = [q1]
val schedule = schedule_session_tests(metas)
val summary = schedule_summary(schedule)
expect(summary.len()).to_be_greater_than(0)
expect(summary).to_contain("Session Schedule:")
expect(summary).to_contain("Total tests: 1")
```

</details>

#### handles mixed QEMU, container, service, and local tests (#TDMN-SCH-025)

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val local1 = test_session_meta_default("test/unit/a_spec.spl")
val local2 = test_session_meta_default("test/unit/b_spec.spl")
val q1 = _make_qemu_meta("test/system/qemu/a_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
val q2 = _make_qemu_meta("test/system/qemu/b_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
val c1 = _make_container_meta("test/container/c_spec.spl", "simple-test:latest")
val s1 = _make_service_meta("test/service/health_spec.spl", "local_web")
var metas: [TestSessionMeta] = [local1, q1, c1, local2, s1, q2]
val schedule = schedule_session_tests(metas)
expect(schedule.total_tests).to_equal(6)
expect(schedule.total_ungrouped).to_equal(2)
expect(schedule.total_groups).to_equal(3)
val session_count = schedule_total_session_tests(schedule)
expect(session_count).to_equal(4)
```

</details>

#### all session paths appear exactly once in flatten (#TDMN-SCH-026)

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val local = test_session_meta_default("test/unit/a_spec.spl")
val q1 = _make_qemu_meta("test/system/qemu/a_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
val q2 = _make_qemu_meta("test/system/qemu/b_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY)
val c1 = _make_container_meta("test/container/c_spec.spl", "simple-test:latest")
var metas: [TestSessionMeta] = [local, q1, q2, c1]
val schedule = schedule_session_tests(metas)
val flat = schedule_flatten(schedule)
expect(flat.len()).to_equal(4)
# All 4 unique paths should be present
var found_q1 = false
var found_q2 = false
var found_c1 = false
var found_local = false
for path in flat:
    if path == "test/system/qemu/a_spec.spl": found_q1 = true
    if path == "test/system/qemu/b_spec.spl": found_q2 = true
    if path == "test/container/c_spec.spl": found_c1 = true
    if path == "test/unit/a_spec.spl": found_local = true
expect(found_q1).to_equal(true)
expect(found_q2).to_equal(true)
expect(found_c1).to_equal(true)
expect(found_local).to_equal(true)
```

</details>

#### scheduler handles many tests in same group (#TDMN-SCH-027)

1. metas push
   - Expected: schedule.total_groups equals `1`
   - Expected: session_count equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var metas: [TestSessionMeta] = []
var i = 0
while i < 20:
    metas.push(_make_qemu_meta("test/system/qemu/test_{i}_spec.spl", "riscv32", REUSE_SHARED_READ_ONLY))
    i = i + 1
val schedule = schedule_session_tests(metas)
expect(schedule.total_groups).to_equal(1)
val session_count = schedule_total_session_tests(schedule)
expect(session_count).to_equal(20)
```

</details>

### Session Scheduler Service and GUI

#### groups service tests by target (#TDMN-SCH-028)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = _make_service_meta("test/service/a_spec.spl", "local_web")
val s2 = _make_service_meta("test/service/b_spec.spl", "local_web")
val s3 = _make_service_meta("test/service/c_spec.spl", "remote_api")
var metas: [TestSessionMeta] = [s1, s2, s3]
val schedule = schedule_session_tests(metas)
val service_groups = schedule_group_for_kind(schedule, SESSION_KIND_SERVICE)
expect(service_groups.len()).to_equal(2)
```

</details>

#### schedules GUI tests as exclusive_reused (#TDMN-SCH-029)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gui = _make_gui_meta("test/gui/window_spec.spl", "headless")
var metas: [TestSessionMeta] = [gui]
val schedule = schedule_session_tests(metas)
expect(schedule.total_groups).to_equal(1)
val groups = schedule.groups
expect(groups[0].priority).to_equal(reuse_priority(REUSE_EXCLUSIVE_REUSED))
```

</details>

#### orders service read-only before GUI exclusive (#TDMN-SCH-030)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gui = _make_gui_meta("test/gui/window_spec.spl", "headless")
val svc = _make_service_meta("test/service/api_spec.spl", "local_web")
var metas: [TestSessionMeta] = [gui, svc]
val schedule = schedule_session_tests(metas)
val groups = schedule.groups
# Service (read_only, priority 0) should be before GUI (exclusive, priority 3)
expect(groups[0].priority).to_be_less_than(groups[1].priority)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
