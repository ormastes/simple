# Bug Add Cli Specification

> 1. dir create all

<!-- sdn-diagram:id=bug_add_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bug_add_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bug_add_cli_spec -> std
bug_add_cli_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bug_add_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bug Add Cli Specification

## Scenarios

### bug-add CLI

#### writes a new open bug into the split-schema active table

1. dir create all
   - Expected: copied is true
   - Expected: result.exit_code equals `0`
   - Expected: content contains `bugs_active |`
   - Expected: content contains `bug_add_cli_fix_001`
   - Expected: content contains `bug_add_cli_fix_001, P2, open`
   - Expected: content contains `src/app/dashboard/assistant_collectors.spl, 0, , bin/simple dashboard assistant`
   - Expected: content contains `bin/simple dashboard assistant`
2. shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = bug_add_cli_fixture_root()
val db_path = bug_add_cli_fixture_db_path(root)
val simple_bin = "/home/ormastes/dev/pub/simple/bin/simple"
val simple_src = "/home/ormastes/dev/pub/simple/src"
val bug_add_main = "/home/ormastes/dev/pub/simple/src/app/bug_add/main.spl"

dir_create_all("{root}/doc/08_tracking/bug")
val copied = file_write(db_path, file_read("doc/08_tracking/bug/bug_db.sdn"))
expect(copied).to_equal(true)

val result = shell("cd {root} && SIMPLE_LIB={simple_src} {simple_bin} run {bug_add_main} --id=bug_add_cli_fix_001 --severity=p2 --title='CLI bug add fix' --file=src/app/dashboard/assistant_collectors.spl --repro='bin/simple dashboard assistant'")
expect(result.exit_code).to_equal(0)

val content = file_read(db_path)
expect(content.contains("bugs_active |")).to_equal(true)
expect(content.contains("bug_add_cli_fix_001")).to_equal(true)
expect(content.contains("bug_add_cli_fix_001, P2, open")).to_equal(true)
expect(content.contains("src/app/dashboard/assistant_collectors.spl, 0, , bin/simple dashboard assistant")).to_equal(true)
expect(content.contains("bin/simple dashboard assistant")).to_equal(true)

shell("rm -rf {root}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/bug_add/bug_add_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bug-add CLI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
