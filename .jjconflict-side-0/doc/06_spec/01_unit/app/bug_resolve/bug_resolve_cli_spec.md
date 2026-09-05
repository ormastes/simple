# Bug Resolve Cli Specification

> 1. shell

<!-- sdn-diagram:id=bug_resolve_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bug_resolve_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bug_resolve_cli_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bug_resolve_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bug Resolve Cli Specification

## Scenarios

### bug-resolve CLI

#### resolves a bug row loaded from the tracked split-schema bug DB

1. shell
   - Expected: created is true
   - Expected: added.exit_code equals `0`
   - Expected: resolved.exit_code equals `0`
   - Expected: content contains `bug_resolve_cli_fix_001, P2, closed`
   - Expected: content contains `2026-04-15`
2. shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = bug_resolve_cli_fixture_root()
val db_path = bug_resolve_cli_fixture_db_path(root)
val simple_bin = "/home/ormastes/dev/pub/simple/bin/simple"
val simple_src = "/home/ormastes/dev/pub/simple/src"
val bug_add_main = "/home/ormastes/dev/pub/simple/src/app/bug_add/main.spl"
val bug_resolve_main = "/home/ormastes/dev/pub/simple/src/app/bug_resolve/main.spl"

shell("mkdir -p '{root}/doc/08_tracking/bug'")
# Write a minimal valid empty bug database so bug_add can load it
val empty_db_content = "bugs_active |id, severity, status, title, file, line, reproducible_by, created_at, updated_at, valid|\n\n\nbug_descriptions |bug_id, line_num, content|\n\n\nbug_fix_strategies |bug_id, line_num, content|\n\n\nbug_investigation_logs |bug_id, line_num, content|\n\n\nbugs |id, severity, status, title, file, line, reproducible_by, created_at, updated_at, valid|\n\n"
val created = _spec_file_write(db_path, empty_db_content)
expect(created).to_equal(true)

val added = shell("cd {root} && SIMPLE_LIB={simple_src} {simple_bin} run {bug_add_main} --id=bug_resolve_cli_fix_001 --severity=p2 --title='CLI bug resolve fix' --file=src/app/dashboard/assistant_collectors.spl --repro='bin/simple dashboard assistant'")
expect(added.exit_code).to_equal(0)

val resolved = shell("cd {root} && SIMPLE_LIB={simple_src} {simple_bin} run {bug_resolve_main} --id=bug_resolve_cli_fix_001 --date=2026-04-15")
expect(resolved.exit_code).to_equal(0)

val content = _spec_file_read(db_path)
expect(content.contains("bug_resolve_cli_fix_001, P2, closed")).to_equal(true)
expect(content.contains("2026-04-15")).to_equal(true)

shell("rm -rf {root}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/bug_resolve/bug_resolve_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bug-resolve CLI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
