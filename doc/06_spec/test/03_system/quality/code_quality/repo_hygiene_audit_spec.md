# Repo Hygiene Audit Specification

> <details>

<!-- sdn-diagram:id=repo_hygiene_audit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=repo_hygiene_audit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

repo_hygiene_audit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=repo_hygiene_audit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Repo Hygiene Audit Specification

## Scenarios

### repository hygiene audit

#### reports empty source dirs, temporary files, and cache directories

<details>
<summary>Executable SPipe</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_repo_hygiene_audit_spec"
val (_clean_out, _clean_err, _clean_code) = rt_process_run("/bin/sh", ["-c", "rm -rf " + root + " && mkdir -p " + root + "/src/app"])
expect(rt_file_write_text(root + "/src/app/main.spl", "fn main():\n    return 0\n")).to_equal(true)

val clean = rt_process_run("bin/simple", ["run", "scripts/audit/repo_hygiene_audit.spl", "--", "--root", root, "--policy", "scripts/audit/repo_hygiene_policy.json"])
expect(clean.2).to_equal(0)
expect(clean.0).to_contain("Unignored temporary files")
expect(clean.0).to_contain("Empty source directories")

val (_mkdir_out, _mkdir_err, _mkdir_code) = rt_process_run("/bin/sh", ["-c", "mkdir -p " + root + "/src/app/empty"])
val empty = rt_process_run("bin/simple", ["run", "scripts/audit/repo_hygiene_audit.spl", "--", "--root", root, "--policy", "scripts/audit/repo_hygiene_policy.json"])
expect(empty.2).to_equal(1)
expect(empty.0).to_contain("src/app/empty")

val allowed = rt_process_run("bin/simple", ["run", "scripts/audit/repo_hygiene_audit.spl", "--", "--root", root, "--policy", "scripts/audit/repo_hygiene_policy.json", "--allow-empty-source-dirs"])
expect(allowed.2).to_equal(0)

expect(rt_file_write_text(root + "/src/app/cache.tmp", "temporary\n")).to_equal(true)
val dirty_file = rt_process_run("bin/simple", ["run", "scripts/audit/repo_hygiene_audit.spl", "--", "--root", root, "--policy", "scripts/audit/repo_hygiene_policy.json", "--allow-empty-source-dirs"])
expect(dirty_file.2).to_equal(1)
expect(dirty_file.0).to_contain("src/app/cache.tmp")

val (_cache_out, _cache_err, _cache_code) = rt_process_run("/bin/sh", ["-c", "mkdir -p " + root + "/src/app/__pycache__ && rm -f " + root + "/src/app/cache.tmp"])
val dirty_dir = rt_process_run("bin/simple", ["run", "scripts/audit/repo_hygiene_audit.spl", "--", "--root", root, "--policy", "scripts/audit/repo_hygiene_policy.json", "--allow-empty-source-dirs"])
expect(dirty_dir.2).to_equal(1)
expect(dirty_dir.0).to_contain("src/app/__pycache__")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/repo_hygiene_audit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- repository hygiene audit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
