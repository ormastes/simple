# Api Consistency Audit Specification

> Tests covering API consistency audit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Api Consistency Audit Specification

## Scenarios

### API consistency audit

#### passes clean fixture APIs and fails hard and advisory violations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes clean fixture APIs and fails hard and advisory violations
   - Expected: rt_file_write_text(root + "/baseline.json", baseline) is true
   - Expected: rt_file_write_text(root + "/src/app/api.spl", "fn list_items():\n    return []\n") is true
   - Expected: clean.2 equals `0`
   - Expected: rt_file_write_text(root + "/src/app/api.spl", "fn get_or_fail():\n    return 1\n") is true
   - Expected: hard.2 equals `1`
   - Expected: rt_file_write_text(root + "/src/app/api.spl", "fn is_ready():\n    return true\n") is true
   - Expected: advisory.2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes clean fixture APIs and fails hard and advisory violations")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering API consistency audit.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c830160c81ec510f36b17df21b063cb038192cc63acf3d8644d36767c83129c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c830160c81ec510f36b17df21b063cb038192cc63acf3d8644d36767c83129c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c830160c81ec510f36b17df21b063cb038192cc63acf3d8644d36767c83129c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/quality/code_quality/api_consistency_audit_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/api_consistency_audit_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/code_quality/api_consistency_audit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/api_consistency_audit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/api_consistency_audit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/quality/code_quality/api_consistency_audit_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes clean fixture APIs and fails hard and advisory violations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
