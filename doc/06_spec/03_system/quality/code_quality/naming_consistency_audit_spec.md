# Naming Consistency Audit Specification

> <details>

<!-- sdn-diagram:id=naming_consistency_audit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=naming_consistency_audit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

naming_consistency_audit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=naming_consistency_audit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Naming Consistency Audit Specification

## Scenarios

### naming consistency audit

#### enforces N001 through N004 against a baseline

<details>
<summary>Executable SPipe</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_naming_consistency_audit_spec"
val (_clean_out, _clean_err, _clean_code) = rt_process_run("/bin/sh", ["-c", "rm -rf " + root + " && mkdir -p " + root + "/src/lib/common"])
expect(rt_file_write_text(root + "/baseline.json", baseline(root, 0, 0, 0, 0))).to_equal(true)
expect(rt_file_write_text(root + "/src/lib/common/api.spl", "pub fn value():\n    return 1\n")).to_equal(true)

val clean = run_audit(root, "")
expect(clean.2).to_equal(0)
expect(clean.0).to_contain("N001 - Verbose get_* prefix: 0")
expect(clean.0).to_contain("N004 - set_from_* constructor pattern: 0")

expect(rt_file_write_text(root + "/src/lib/common/api.spl", "pub fn get_value():\n    return 1\npub fn set_from_list(values: [text]):\n    return values\n")).to_equal(true)
val naming = run_audit(root, root + "/fixes.json")
expect(naming.2).to_equal(1)
expect(naming.0).to_contain("N001 - Verbose get_* prefix: 1")
expect(naming.0).to_contain("N004 - set_from_* constructor pattern: 1")
expect(naming.0).to_contain("N001 violation count increased from 0 to 1")
val fixes = rt_file_read_text(root + "/fixes.json")
expect(fixes).to_contain("\"current\":\"get_value\"")
expect(fixes).to_contain("\"suggested\":\"value\"")

val (_dirs_out, _dirs_err, _dirs_code) = rt_process_run("/bin/sh", ["-c", "mkdir -p " + root + "/src/lib/common/fs " + root + "/src/lib/common/file_system"])
val module_names = run_audit(root, "")
expect(module_names.2).to_equal(1)
expect(module_names.0).to_contain("N002 - Module naming inconsistency: 1")

val (_dup_out, _dup_err, _dup_code) = rt_process_run("/bin/sh", ["-c", "mkdir -p " + root + "/src/lib/other"])
expect(rt_file_write_text(root + "/src/lib/common/api.spl", "pub fn is_ready(value: text):\n    return true\n")).to_equal(true)
expect(rt_file_write_text(root + "/src/lib/other/api.spl", "pub fn is_ready(value: text):\n    return true\n")).to_equal(true)
val duplicate = run_audit(root, "")
expect(duplicate.2).to_equal(1)
expect(duplicate.0).to_contain("N003 - Duplicate predicates: 1")
expect(duplicate.0).to_contain("N003 violation count increased from 0 to 1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/naming_consistency_audit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- naming consistency audit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
