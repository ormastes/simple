# Bug Resolve Cli Specification

> Tests covering bug-resolve CLI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bug Resolve Cli Specification

## Scenarios

### bug-resolve CLI

#### resolves a bug row loaded from the tracked split-schema bug DB

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves a bug row loaded from the tracked split-schema bug DB
   - Expected: simple_bin equals `cwd() + "/bin/simple"`
   - Expected: simple_src equals `cwd() + "/src"`
   - Expected: bug_add_main equals `cwd() + "/src/app/bug_add/main.spl"`
   - Expected: bug_resolve_main equals `cwd() + "/src/app/bug_resolve/main.spl"`
   - Expected: created is true
   - Expected: added.exit_code equals `0`
   - Expected: resolved.exit_code equals `0`
   - Expected: content contains `bug_resolve_cli_fix_001, P2, closed`
   - Expected: content contains `2026-04-15`
   - Expected: comparison.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a bug row loaded from the tracked split-schema bug DB")
val root = bug_resolve_cli_fixture_root()
val db_path = bug_resolve_cli_fixture_db_path(root)
val project_root = cwd()
val simple_bin = project_root + "/bin/simple"
val simple_src = project_root + "/src"
val bug_add_main = project_root + "/src/app/bug_add/main.spl"
val bug_resolve_main = project_root + "/src/app/bug_resolve/main.spl"
expect(simple_bin).to_equal(cwd() + "/bin/simple")
expect(simple_src).to_equal(cwd() + "/src")
expect(bug_add_main).to_equal(cwd() + "/src/app/bug_add/main.spl")
expect(bug_resolve_main).to_equal(cwd() + "/src/app/bug_resolve/main.spl")

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

val marker = "bug_resolve_cli_fix_001, P2, closed"
val marker_at = content.index_of(marker)
val extracted = if marker_at >= 0: content.substring(marker_at, marker_at + marker.len()) else: ""
val capture = UntypedCapture(label: "bug-resolve-cli-db-row-status", raw_value: extracted, source_kind: "log_line")
val evidence = untyped_capture_to_canonical(capture, "bug_resolve_cli_spec/db-row-status")
val comparison = compare_evidence(evidence, oracle_spec("bug_resolve_cli_spec/db-row-status", [
    check_exact("value", marker)
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)

shell("rm -rf {root}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/bug_resolve/bug_resolve_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bug-resolve CLI.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c1c653608f41f986f4cd080fb5037ce768422c0e35658fddc33e5ca9fe14244f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c1c653608f41f986f4cd080fb5037ce768422c0e35658fddc33e5ca9fe14244f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c1c653608f41f986f4cd080fb5037ce768422c0e35658fddc33e5ca9fe14244f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/unit/app/bug_resolve/bug_resolve_cli_spec.spl
mirror: doc/06_spec/unit/app/bug_resolve/bug_resolve_cli_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/bug_resolve/bug_resolve_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/bug_resolve/bug_resolve_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/bug_resolve/bug_resolve_cli_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
