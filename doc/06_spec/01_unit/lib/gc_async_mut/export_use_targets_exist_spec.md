# Export Use Targets Exist Specification

> Tests covering export use targets exist (dangling-facade defect class).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Export Use Targets Exist Specification

## Scenarios

### export use targets exist (dangling-facade defect class)

#### no export-use-star in gc_async_mut names a nonexistent module

- no export-use-star in gc_async_mut names a nonexistent module
   - Expected: unexpected.join(", ") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("no export-use-star in gc_async_mut names a nonexistent module")
val missing = scan_missing("src/lib/gc_async_mut")
var unexpected: [text] = []
for m in missing:
    var allowed = false
    for a in allowed_open():
        if a == m:
            allowed = true
    if not allowed:
        unexpected.push(m)
expect(unexpected.join(", ")).to_equal("")
```

</details>

#### the known-open allowlist does not silently grow

- the known-open allowlist does not silently grow
   - Expected: allowed_open().len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the known-open allowlist does not silently grow")
expect(allowed_open().len()).to_equal(3)
```

</details>

#### the scan is non-vacuous - it parses real export-use lines

- the scan is non-vacuous - it parses real export-use lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the scan is non-vacuous - it parses real export-use lines")
val cmd = "/usr/bin/grep -rhcE '^export use std[.]' src/lib/gc_async_mut " +
    "--include=*.spl 2>/dev/null | paste -sd+ - | bc"
val res = process_run("sh", ["-c", cmd])
val n = res.stdout.trim().to_i64()
# A run that examined zero export-use lines proves nothing; treat it as
# a failure, never as a pass (see BRIEF: non-vacuity is absolute).
expect(n > 20).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/export_use_targets_exist_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering export use targets exist (dangling-facade defect class).
- export use targets exist (dangling-facade defect class)

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d3821395a76b4dcc0dd08d2f744d0951b91a3ea926947780c80518ac2628df00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d3821395a76b4dcc0dd08d2f744d0951b91a3ea926947780c80518ac2628df00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d3821395a76b4dcc0dd08d2f744d0951b91a3ea926947780c80518ac2628df00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gc_async_mut/export_use_targets_exist_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/export_use_targets_exist_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/export_use_targets_exist_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/export_use_targets_exist_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/export_use_targets_exist_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/export_use_targets_exist_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no export-use-star in gc_async_mut names a nonexistent module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/export_use_targets_exist_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the known-open allowlist does not silently grow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/export_use_targets_exist_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the scan is non-vacuous - it parses real export-use lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
