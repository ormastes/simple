# Naming Consistency Audit Specification

> Tests covering naming consistency audit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Naming Consistency Audit Specification

## Scenarios

### naming consistency audit

#### enforces N001 through N004 against a baseline

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- enforces N001 through N004 against a baseline
   - Expected: rt_file_write_text(root + "/baseline.json", baseline(root, 0, 0, 0, 0)) is true
   - Expected: rt_file_write_text(root + "/src/lib/common/api.spl", "pub fn value():\n    return 1\n") is true
   - Expected: clean.2 equals `0`
   - Expected: rt_file_write_text(root + "/src/lib/common/api.spl", "pub fn get_value():\n    return 1\npub fn set_from_list(values: [text]):\n    return values\n") is true
   - Expected: naming.2 equals `1`
   - Expected: module_names.2 equals `1`
   - Expected: rt_file_write_text(root + "/src/lib/common/api.spl", "pub fn is_ready(value: text):\n    return true\n") is true
   - Expected: rt_file_write_text(root + "/src/lib/other/api.spl", "pub fn is_ready(value: text):\n    return true\n") is true
   - Expected: duplicate.2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enforces N001 through N004 against a baseline")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering naming consistency audit.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a731771a382a68ef83f18d56b79972c81cbeab13b798c3672f348e39641e71a5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a731771a382a68ef83f18d56b79972c81cbeab13b798c3672f348e39641e71a5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a731771a382a68ef83f18d56b79972c81cbeab13b798c3672f348e39641e71a5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/quality/code_quality/naming_consistency_audit_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/naming_consistency_audit_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/code_quality/naming_consistency_audit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/naming_consistency_audit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/naming_consistency_audit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/quality/code_quality/naming_consistency_audit_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enforces N001 through N004 against a baseline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
