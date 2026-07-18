# Api Consistency Audit Specification

> <details>

<!-- sdn-diagram:id=api_consistency_audit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=api_consistency_audit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

api_consistency_audit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=api_consistency_audit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Api Consistency Audit Specification

## Scenarios

### API consistency audit

#### passes clean fixture APIs and fails hard and advisory violations

<details>
<summary>Executable SPipe</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_api_consistency_audit_spec"
val (_clean_out, _clean_err, _clean_code) = rt_process_run("/bin/sh", ["-c", "rm -rf " + root + " && mkdir -p " + root + "/src/app"])
val baseline =
    "{\n" +
    "  \"advisory_predicate_prefix_debt\": 0,\n" +
    "  \"advisory_predicate_prefix_debt_by_root\": {\n" +
    "    \"" + root + "/src/app\": 0\n" +
    "  }\n" +
    "}\n"
expect(rt_file_write_text(root + "/baseline.json", baseline)).to_equal(true)

expect(rt_file_write_text(root + "/src/app/api.spl", "fn list_items():\n    return []\n")).to_equal(true)
val clean = rt_process_run("bin/simple", ["run", "scripts/audit/api_consistency_audit.spl", "--", "--scan-root", root + "/src/app", "--baseline", root + "/baseline.json"])
expect(clean.2).to_equal(0)
expect(clean.0).to_contain("Hard violations: 0")
expect(clean.0).to_contain("Advisory predicate-prefix debt: 0")

expect(rt_file_write_text(root + "/src/app/api.spl", "fn get_or_fail():\n    return 1\n")).to_equal(true)
val hard = rt_process_run("bin/simple", ["run", "scripts/audit/api_consistency_audit.spl", "--", "--scan-root", root + "/src/app", "--baseline", root + "/baseline.json"])
expect(hard.2).to_equal(1)
expect(hard.0).to_contain("Hard violations: 1")
expect(hard.0).to_contain("Use fetch for required lookup")

expect(rt_file_write_text(root + "/src/app/api.spl", "fn is_ready():\n    return true\n")).to_equal(true)
val advisory = rt_process_run("bin/simple", ["run", "scripts/audit/api_consistency_audit.spl", "--", "--scan-root", root + "/src/app", "--baseline", root + "/baseline.json"])
expect(advisory.2).to_equal(1)
expect(advisory.0).to_contain("Advisory predicate-prefix debt: 1")
expect(advisory.0).to_contain("advisory predicate-prefix debt increased from 0 to 1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/api_consistency_audit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- API consistency audit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
