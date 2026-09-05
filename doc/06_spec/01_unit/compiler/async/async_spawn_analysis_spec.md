# async_spawn_analysis_spec

> Purpose: Prove that is_in_list utility.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# async_spawn_analysis_spec

Purpose: Prove that is_in_list utility.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/async/async_spawn_analysis_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that is_in_list utility.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### is_in_list utility

#### finds existing name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds existing name
- Verify: finds existing name
   - Expected: is_in_list("main", ["main", "setup", "init"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("finds existing name")
step("Verify: finds existing name")
# @req: REQ-COMP-IS-IN-LIST-UTILITY-001
expect(is_in_list("main", ["main", "setup", "init"])).to_equal(true)
```

</details>

#### returns false for missing name

- returns false for missing name
- Verify: returns false for missing name
   - Expected: is_in_list("handler", ["main", "setup"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns false for missing name")
step("Verify: returns false for missing name")
expect(is_in_list("handler", ["main", "setup"])).to_equal(false)
```

</details>

#### returns false for empty list

- returns false for empty list
- Verify: returns false for empty list
   - Expected: is_in_list("main", []) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns false for empty list")
step("Verify: returns false for empty list")
expect(is_in_list("main", [])).to_equal(false)
```

</details>

### get_boot_spawn_count lookup

#### returns count for existing task

- returns count for existing task
- Verify: returns count for existing task
   - Expected: get_boot_spawn_count("uart_rx", names, counts) equals `3`
   - Expected: get_boot_spawn_count("spi_tx", names, counts) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns count for existing task")
step("Verify: returns count for existing task")
val names = ["uart_rx", "spi_tx"]
val counts = [3, 2]
expect(get_boot_spawn_count("uart_rx", names, counts)).to_equal(3)
expect(get_boot_spawn_count("spi_tx", names, counts)).to_equal(2)
```

</details>

#### returns zero for unknown task

- returns zero for unknown task
- Verify: returns zero for unknown task
   - Expected: get_boot_spawn_count("unknown", names, counts) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns zero for unknown task")
step("Verify: returns zero for unknown task")
val names = ["uart_rx"]
val counts = [3]
expect(get_boot_spawn_count("unknown", names, counts)).to_equal(0)
```

</details>

#### returns zero for empty arrays

- returns zero for empty arrays
- Verify: returns zero for empty arrays
   - Expected: get_boot_spawn_count("any", [], []) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns zero for empty arrays")
step("Verify: returns zero for empty arrays")
expect(get_boot_spawn_count("any", [], [])).to_equal(0)
```

</details>

### Init phase validation

#### passes when all spawns in init-reachable

- passes when all spawns in init-reachable
- Verify: passes when all spawns in init-reachable
   - Expected: result.has_errors is false
   - Expected: result.total_spawns equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes when all spawns in init-reachable")
step("Verify: passes when all spawns in init-reachable")
val sa = make_clean_analysis()
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(false)
expect(result.total_spawns).to_equal(2)
```

</details>

#### errors when spawn outside init-reachable

- errors when spawn outside init-reachable
- Verify: errors when spawn outside init-reachable
   - Expected: result.has_errors is true
   - Expected: found_outside is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("errors when spawn outside init-reachable")
step("Verify: errors when spawn outside init-reachable")
val sa = make_analysis_with_outside_spawn()
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(true)
var found_outside = false
for diag in result.diagnostics:
    if diag.message.contains("outside init phase"):
        found_outside = true
expect(found_outside).to_equal(true)
```

</details>

#### errors when spawn after await

- errors when spawn after await
- Verify: errors when spawn after await
   - Expected: result.has_errors is true
   - Expected: found_after is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("errors when spawn after await")
step("Verify: errors when spawn after await")
val sa = make_analysis_with_after_await()
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(true)
var found_after = false
for diag in result.diagnostics:
    if diag.message.contains("after await"):
        found_after = true
expect(found_after).to_equal(true)
```

</details>

### Instance limits

#### passes when spawns within instance count

- passes when spawns within instance count
- Verify: passes when spawns within instance count
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes when spawns within instance count")
step("Verify: passes when spawns within instance count")
val sa = SpawnAnalysis(
    init_functions: ["main"],
    init_reachable: ["main"],
    spawn_sites: [make_spawn_site("uart_rx", "main", false)],
    task_infos: [make_task_info("uart_rx", 4)],
    group_infos: [],
    boot_spawn_names: ["uart_rx"],
    boot_spawn_counts: [2]
)
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(false)
```

</details>

#### passes when spawns equal instance count

- passes when spawns equal instance count
- Verify: passes when spawns equal instance count
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes when spawns equal instance count")
step("Verify: passes when spawns equal instance count")
val sa = SpawnAnalysis(
    init_functions: ["main"],
    init_reachable: ["main"],
    spawn_sites: [make_spawn_site("uart_rx", "main", false)],
    task_infos: [make_task_info("uart_rx", 3)],
    group_infos: [],
    boot_spawn_names: ["uart_rx"],
    boot_spawn_counts: [3]
)
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(false)
```

</details>

#### errors when spawns exceed instance count

- errors when spawns exceed instance count
- Verify: errors when spawns exceed instance count
   - Expected: result.has_errors is true
   - Expected: found_instance_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("errors when spawns exceed instance count")
step("Verify: errors when spawns exceed instance count")
val sa = SpawnAnalysis(
    init_functions: ["main"],
    init_reachable: ["main"],
    spawn_sites: [make_spawn_site("uart_rx", "main", false)],
    task_infos: [make_task_info("uart_rx", 2)],
    group_infos: [],
    boot_spawn_names: ["uart_rx"],
    boot_spawn_counts: [5]
)
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(true)
var found_instance_error = false
for diag in result.diagnostics:
    if diag.message.contains("spawned 5 times") and diag.message.contains("instances=2"):
        found_instance_error = true
expect(found_instance_error).to_equal(true)
```

</details>

### Group capacity

#### passes when group total within cap

- passes when group total within cap
- Verify: passes when group total within cap
   - Expected: result.has_errors is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes when group total within cap")
step("Verify: passes when group total within cap")
val sa = SpawnAnalysis(
    init_functions: ["main"],
    init_reachable: ["main"],
    spawn_sites: [
        make_spawn_site("uart_rx", "main", false),
        make_spawn_site("spi_tx", "main", false)
    ],
    task_infos: [
        make_task_info_grouped("uart_rx", 4, "io_pool"),
        make_task_info_grouped("spi_tx", 4, "io_pool")
    ],
    group_infos: [make_group("io_pool", 6, ["uart_rx", "spi_tx"])],
    boot_spawn_names: ["uart_rx", "spi_tx"],
    boot_spawn_counts: [2, 3]
)
val result = verify_spawn_bounds(sa)
# Grouped tasks skip individual instance check (group != nil)
# Group total 2+3=5 <= 6 cap
expect(result.has_errors).to_equal(false)
```

</details>

#### errors when group total exceeds cap

- errors when group total exceeds cap
- Verify: errors when group total exceeds cap
   - Expected: result.has_errors is true
   - Expected: found_group_error is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("errors when group total exceeds cap")
step("Verify: errors when group total exceeds cap")
val sa = SpawnAnalysis(
    init_functions: ["main"],
    init_reachable: ["main"],
    spawn_sites: [
        make_spawn_site("uart_rx", "main", false),
        make_spawn_site("spi_tx", "main", false)
    ],
    task_infos: [
        make_task_info_grouped("uart_rx", 10, "io_pool"),
        make_task_info_grouped("spi_tx", 10, "io_pool")
    ],
    group_infos: [make_group("io_pool", 4, ["uart_rx", "spi_tx"])],
    boot_spawn_names: ["uart_rx", "spi_tx"],
    boot_spawn_counts: [3, 3]
)
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(true)
var found_group_error = false
for diag in result.diagnostics:
    if diag.message.contains("task group") and diag.message.contains("cap=4"):
        found_group_error = true
expect(found_group_error).to_equal(true)
```

</details>

### Combined checks

#### reports multiple errors at once

- reports multiple errors at once
- Verify: reports multiple errors at once
   - Expected: result.has_errors is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports multiple errors at once")
step("Verify: reports multiple errors at once")
val sa = SpawnAnalysis(
    init_functions: ["main"],
    init_reachable: ["main"],
    spawn_sites: [
        make_spawn_site("uart_rx", "main", true),
        make_spawn_site("spi_tx", "handler", false)
    ],
    task_infos: [
        make_task_info("uart_rx", 1),
        make_task_info("spi_tx", 1)
    ],
    group_infos: [],
    boot_spawn_names: ["uart_rx"],
    boot_spawn_counts: [1]
)
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(true)
# Should have at least 2 errors: after-await + outside init
expect(result.diagnostics.len()).to_be_greater_than(1)
```

</details>

#### passes clean module with no issues

- passes clean module with no issues
- Verify: passes clean module with no issues
   - Expected: result.has_errors is false
   - Expected: result.diagnostics.len() equals `0`
   - Expected: result.total_spawns equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("passes clean module with no issues")
step("Verify: passes clean module with no issues")
val sa = make_clean_analysis()
val result = verify_spawn_bounds(sa)
expect(result.has_errors).to_equal(false)
expect(result.diagnostics.len()).to_equal(0)
expect(result.total_spawns).to_equal(2)
```

</details>

### Data structure construction

#### creates SpawnSite correctly

- creates SpawnSite correctly
- Verify: creates SpawnSite correctly
   - Expected: site.task_name equals `uart_rx`
   - Expected: site.caller_name equals `main`
   - Expected: site.is_after_await is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates SpawnSite correctly")
step("Verify: creates SpawnSite correctly")
val site = make_spawn_site("uart_rx", "main", false)
expect(site.task_name).to_equal("uart_rx")
expect(site.caller_name).to_equal("main")
expect(site.is_after_await).to_equal(false)
```

</details>

#### creates TaskInfo correctly

- creates TaskInfo correctly
- Verify: creates TaskInfo correctly
   - Expected: info.name equals `uart_rx`
   - Expected: info.instances equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates TaskInfo correctly")
step("Verify: creates TaskInfo correctly")
val info = make_task_info("uart_rx", 4)
expect(info.name).to_equal("uart_rx")
expect(info.instances).to_equal(4)
expect(info.group).to_be_nil()
```

</details>

#### creates TaskGroupInfo correctly

- creates TaskGroupInfo correctly
- Verify: creates TaskGroupInfo correctly
   - Expected: group.name equals `io_pool`
   - Expected: group.cap equals `8`
   - Expected: group.members.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates TaskGroupInfo correctly")
step("Verify: creates TaskGroupInfo correctly")
val group = make_group("io_pool", 8, ["uart_rx", "spi_tx"])
expect(group.name).to_equal("io_pool")
expect(group.cap).to_equal(8)
expect(group.members.len()).to_equal(2)
```

</details>

#### creates SpawnAnalysis correctly

- creates SpawnAnalysis correctly
- Verify: creates SpawnAnalysis correctly
   - Expected: sa.init_functions.len() equals `1`
   - Expected: sa.init_reachable.len() equals `2`
   - Expected: sa.spawn_sites.len() equals `2`
   - Expected: sa.task_infos.len() equals `2`
   - Expected: sa.boot_spawn_names.len() equals `2`
   - Expected: sa.boot_spawn_counts.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates SpawnAnalysis correctly")
step("Verify: creates SpawnAnalysis correctly")
val sa = make_clean_analysis()
expect(sa.init_functions.len()).to_equal(1)
expect(sa.init_reachable.len()).to_equal(2)
expect(sa.spawn_sites.len()).to_equal(2)
expect(sa.task_infos.len()).to_equal(2)
expect(sa.boot_spawn_names.len()).to_equal(2)
expect(sa.boot_spawn_counts.len()).to_equal(2)
```

</details>

### compute_init_reachable

#### includes init functions themselves

- includes init functions themselves
- Verify: includes init functions themselves
   - Expected: is_in_list("main", reachable) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("includes init functions themselves")
step("Verify: includes init functions themselves")
val reachable = compute_init_reachable(["main"], [], [])
expect(is_in_list("main", reachable)).to_equal(true)
```

</details>

#### follows direct calls

- follows direct calls
- Verify: follows direct calls
   - Expected: is_in_list("main", reachable) is true
   - Expected: is_in_list("setup", reachable) is true
   - Expected: is_in_list("init_hw", reachable) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("follows direct calls")
step("Verify: follows direct calls")
val callers = ["main", "main"]
val callees = ["setup", "init_hw"]
val reachable = compute_init_reachable(["main"], callers, callees)
expect(is_in_list("main", reachable)).to_equal(true)
expect(is_in_list("setup", reachable)).to_equal(true)
expect(is_in_list("init_hw", reachable)).to_equal(true)
```

</details>

#### follows transitive calls

- follows transitive calls
- Verify: follows transitive calls
   - Expected: is_in_list("init_hw", reachable) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("follows transitive calls")
step("Verify: follows transitive calls")
val callers = ["main", "setup"]
val callees = ["setup", "init_hw"]
val reachable = compute_init_reachable(["main"], callers, callees)
expect(is_in_list("init_hw", reachable)).to_equal(true)
```

</details>

#### excludes unreachable functions

- excludes unreachable functions
- Verify: excludes unreachable functions
   - Expected: is_in_list("setup", reachable) is true
   - Expected: is_in_list("handler", reachable) is false
   - Expected: is_in_list("process", reachable) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("excludes unreachable functions")
step("Verify: excludes unreachable functions")
val callers = ["main", "handler"]
val callees = ["setup", "process"]
val reachable = compute_init_reachable(["main"], callers, callees)
expect(is_in_list("setup", reachable)).to_equal(true)
expect(is_in_list("handler", reachable)).to_equal(false)
expect(is_in_list("process", reachable)).to_equal(false)
```

</details>

### Spawn analysis formatting

#### produces non-empty report

- produces non-empty report
- Verify: produces non-empty report


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("produces non-empty report")
step("Verify: produces non-empty report")
val sa = make_clean_analysis()
val report = format_spawn_analysis(sa)
expect(report.len()).to_be_greater_than(0)
expect(report).to_contain("Spawn Analysis:")
expect(report).to_contain("Init functions:")
expect(report).to_contain("Spawn sites:")
```

</details>

#### formats verification result

- formats verification result
- Verify: formats verification result


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("formats verification result")
step("Verify: formats verification result")
val sa = make_clean_analysis()
val result = verify_spawn_bounds(sa)
val output = format_spawn_verify_result(result)
expect(output).to_contain("Spawn Verification:")
expect(output).to_contain("All spawn checks passed.")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-IS-IN-LIST-UTILITY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `664e89afdfe3e6732206991b289b41f42ec538e12d91878e8de21c14b462597a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `664e89afdfe3e6732206991b289b41f42ec538e12d91878e8de21c14b462597a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `664e89afdfe3e6732206991b289b41f42ec538e12d91878e8de21c14b462597a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/async/async_spawn_analysis_spec.spl
mirror: doc/06_spec/01_unit/compiler/async/async_spawn_analysis_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/async/async_spawn_analysis_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/async/async_spawn_analysis_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/async/async_spawn_analysis_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/async/async_spawn_analysis_spec.spl:132:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds existing name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/async/async_spawn_analysis_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false for missing name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/async/async_spawn_analysis_spec.spl:145:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns false for empty list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
