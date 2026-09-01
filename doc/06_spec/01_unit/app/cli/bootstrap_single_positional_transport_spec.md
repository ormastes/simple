# Bootstrap Single Positional Transport Specification

> Tests covering bootstrap single-file native build transport.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Single Positional Transport Specification

## Scenarios

### bootstrap single-file native build transport

#### transports one positional input file into a compiled artifact

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compile a single positional source file end to end
   - Expected: code equals `0`
   - Expected: smf_bytes > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("compile a single positional source file end to end")
val work = "/tmp/sspec_baa_bootstrap_transport"
val _m = rt_process_run("/bin/mkdir", ["-p", work])
val entry = work + "/entry.spl"
val artifact = work + "/entry.smf"
val probe = "fn main() -> i64:\n    return 0\n"
val _w = rt_file_write_text(entry, probe)
val (_out, _err, code) = rt_process_run("bin/simple", ["compile", entry, "-o", artifact])
expect(code).to_equal(0)
val smf_bytes = rt_file_size(artifact) ?? 0
expect(smf_bytes > 0).to_equal(true)
```

</details>

#### rejects a positional input that does not exist

- compile a missing positional input and observe failure
   - Expected: code2 != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("compile a missing positional input and observe failure")
val work = "/tmp/sspec_baa_bootstrap_transport"
val (_out2, _err2, code2) = rt_process_run("bin/simple", ["compile", work + "/missing.spl", "-o", work + "/missing.smf"])
expect(code2 != 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/bootstrap_single_positional_transport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bootstrap single-file native build transport.
- bootstrap single-file native build transport

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1890528cb993689df5f7dd576ae1722f7befa1e4d258a62b06c4efe88b9ef85f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1890528cb993689df5f7dd576ae1722f7befa1e4d258a62b06c4efe88b9ef85f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1890528cb993689df5f7dd576ae1722f7befa1e4d258a62b06c4efe88b9ef85f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/cli/bootstrap_single_positional_transport_spec.spl
mirror: doc/06_spec/01_unit/app/cli/bootstrap_single_positional_transport_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/bootstrap_single_positional_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/bootstrap_single_positional_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/bootstrap_single_positional_transport_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/cli/bootstrap_single_positional_transport_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transports one positional input file into a compiled artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/bootstrap_single_positional_transport_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a positional input that does not exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
