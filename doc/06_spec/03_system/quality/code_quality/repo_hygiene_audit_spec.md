# Repo Hygiene Audit Specification

> Tests covering repository hygiene audit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Repo Hygiene Audit Specification

## Scenarios

### repository hygiene audit

#### reports empty source dirs, temporary files, and cache directories

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports empty source dirs, temporary files, and cache directories
   - Expected: rt_file_write_text(root + "/src/app/main.spl", "fn main():\n    return 0\n") is true
   - Expected: clean.2 equals `0`
   - Expected: empty.2 equals `1`
   - Expected: allowed.2 equals `0`
   - Expected: rt_file_write_text(root + "/src/app/cache.tmp", "temporary\n") is true
   - Expected: dirty_file.2 equals `1`
   - Expected: dirty_dir.2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports empty source dirs, temporary files, and cache directories")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering repository hygiene audit.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1887b73bfc5b7b6ed019878ba8e4c8183338658f544f7f543b953801193ea1d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1887b73bfc5b7b6ed019878ba8e4c8183338658f544f7f543b953801193ea1d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1887b73bfc5b7b6ed019878ba8e4c8183338658f544f7f543b953801193ea1d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/quality/code_quality/repo_hygiene_audit_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/repo_hygiene_audit_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/code_quality/repo_hygiene_audit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/repo_hygiene_audit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/repo_hygiene_audit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/quality/code_quality/repo_hygiene_audit_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports empty source dirs, temporary files, and cache directories' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
