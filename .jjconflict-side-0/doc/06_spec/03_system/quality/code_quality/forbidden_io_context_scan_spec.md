# Forbidden Io Context Scan Specification

> Tests covering forbidden-io context scan.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Forbidden Io Context Scan Specification

## Scenarios

### forbidden-io context scan

#### reports a clean run when no forbidden-context I/O violation exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a clean run when no forbidden-context I/O violation exists
   - Expected: result.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports a clean run when no forbidden-context I/O violation exists")
val result = rt_process_run("bin/simple", ["run", "scripts/audit/forbidden_io_context_scan.spl"])
expect(result.2).to_equal(0)
```

</details>

#### catches a real direct-acquire violation (interrupt-context fn calling apk_load_facet) end-to-end

- catches a real direct-acquire violation (interrupt-context fn calling apk_load_facet) end-to-end
   - Expected: result.2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("catches a real direct-acquire violation (interrupt-context fn calling apk_load_facet) end-to-end")
file_write(DIRECT_PROBE_PATH, DIRECT_PROBE_SOURCE)
val result = rt_process_run("bin/simple", ["run", "scripts/audit/forbidden_io_context_scan.spl"])
file_delete(DIRECT_PROBE_PATH)

expect(result.2).to_equal(1)
expect(result.0).to_contain("E-APACK008")
expect(result.0).to_contain("direct-acquire")
expect(result.0).to_contain("probe_forbidden_io_direct_spec_fixture")
expect(result.0).to_contain("apk_load_facet")
```

</details>

#### catches a real transitive-acquire violation (@noalloc fn calling a helper that directly acquires) end-to-end

- catches a real transitive-acquire violation (@noalloc fn calling a helper that directly acquires) end-to-end
   - Expected: result.2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("catches a real transitive-acquire violation (@noalloc fn calling a helper that directly acquires) end-to-end")
file_write(TRANSITIVE_PROBE_PATH, TRANSITIVE_PROBE_SOURCE)
val result = rt_process_run("bin/simple", ["run", "scripts/audit/forbidden_io_context_scan.spl"])
file_delete(TRANSITIVE_PROBE_PATH)

expect(result.2).to_equal(1)
expect(result.0).to_contain("E-APACK008")
expect(result.0).to_contain("transitive-acquire")
expect(result.0).to_contain("probe_forbidden_io_transitive_spec_fixture")
expect(result.0).to_contain("apk_load_aspect_manual")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/forbidden_io_context_scan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering forbidden-io context scan.
- forbidden-io context scan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `6f8e8322033f0527de4f2f5e1358bac9423a86e5add8692fd3bc837ffdfd55f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6f8e8322033f0527de4f2f5e1358bac9423a86e5add8692fd3bc837ffdfd55f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6f8e8322033f0527de4f2f5e1358bac9423a86e5add8692fd3bc837ffdfd55f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/quality/code_quality/forbidden_io_context_scan_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/forbidden_io_context_scan_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/code_quality/forbidden_io_context_scan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/forbidden_io_context_scan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/forbidden_io_context_scan_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/quality/code_quality/forbidden_io_context_scan_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a clean run when no forbidden-context I/O violation exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/forbidden_io_context_scan_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'catches a real direct-acquire violation (interrupt-context fn calling apk_load_facet) end-to-end' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/forbidden_io_context_scan_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'catches a real transitive-acquire violation (@noalloc fn calling a helper that directly acquires) end-to-end' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
