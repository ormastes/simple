# Stats Bug Schema Specification

> 1. dir create all

<!-- sdn-diagram:id=stats_bug_schema_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stats_bug_schema_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stats_bug_schema_spec -> std
stats_bug_schema_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stats_bug_schema_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stats Bug Schema Specification

## Scenarios

### Bug stats split-table schema

#### counts open and critical bugs across bugs_active and bugs

1. dir create all
   - Expected: file_write(db_path, bug_db) is true
   - Expected: file_write(script_path, script) is true
   - Expected: result.exit_code equals `0`
   - Expected: result.stdout contains `total=4`
   - Expected: result.stdout contains `open=2`
   - Expected: result.stdout contains `critical=2`
   - Expected: result.stdout contains `fixed=2`
   - Expected: result.stdout contains `dyn_open=2`
   - Expected: result.stdout contains `dyn_critical=2`
2. shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = stats_fixture_root()
val db_path = stats_fixture_db_path(root)
val script_path = "{root}/check_bug_stats.spl"
val simple_bin = "/home/ormastes/dev/pub/simple/bin/simple"
val simple_src = "/home/ormastes/dev/pub/simple/src"

dir_create_all("{root}/doc/08_tracking/bug")
val bug_db = "# fixture\n\nbugs_active |id, severity, status, title, file, line, description, reproducible_by|\n    live_001, P1, open, Live bug, src/live.spl, 1, Live desc, live_spec\n    triage_001, P2, Investigating, Triage bug, src/triage.spl, 2, Triage desc, triage_spec\n\nbugs |id, severity, status, title, file, line, description, reproducible_by|\n    fixed_001, P2, fixed, Fixed bug, src/fixed.spl, 3, Fixed desc, fixed_spec\n    closed_critical_001, P0, closed, Closed critical bug, src/closed.spl, 4, Closed desc, closed_spec\n"
expect(file_write(db_path, bug_db)).to_equal(true)

val script = "use compiler.tools.stats.db_aggregator (collect_bug_stats)\nuse compiler.tools.stats.dynamic (get_bug_open, get_bug_critical)\nfn main() -> i64:\n    val stats = collect_bug_stats()\n    print \"total={stats.total};open={stats.open};critical={stats.critical};fixed={stats.fixed};dyn_open={get_bug_open()};dyn_critical={get_bug_critical()}\"\n    0\n"
expect(file_write(script_path, script)).to_equal(true)

val result = shell("cd {root} && SIMPLE_LIB={simple_src} {simple_bin} run {script_path}")
expect(result.exit_code).to_equal(0)
expect(result.stdout.contains("total=4")).to_equal(true)
expect(result.stdout.contains("open=2")).to_equal(true)
expect(result.stdout.contains("critical=2")).to_equal(true)
expect(result.stdout.contains("fixed=2")).to_equal(true)
expect(result.stdout.contains("dyn_open=2")).to_equal(true)
expect(result.stdout.contains("dyn_critical=2")).to_equal(true)

shell("rm -rf {root}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/stats_bug_schema_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bug stats split-table schema

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
