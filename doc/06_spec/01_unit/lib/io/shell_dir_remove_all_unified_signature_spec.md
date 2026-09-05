# Shell Dir Remove All Unified Signature Specification

> Tests covering dir_remove_all unified signature, shell unified signature.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Dir Remove All Unified Signature Specification

## Scenarios

### dir_remove_all unified signature

#### dir_ops and io_runtime variants both return bool true on success

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dir_ops and io_runtime variants both return bool true on success
   - Expected: ra is true
   - Expected: rb is true
   - Expected: dir_exists(a) is false
   - Expected: dir_exists(b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dir_ops and io_runtime variants both return bool true on success")
val a = "/tmp/dir_remove_all_unified_spec_a"
val b = "/tmp/dir_remove_all_unified_spec_b"
dir_create_all(a + "/nested")
dir_create_all(b + "/nested")
file_write(a + "/nested/f.txt", "x")
file_write(b + "/nested/f.txt", "x")
val ra = dir_remove_all(a)
val rb = rt_dir_remove_all_variant(b)
expect(ra).to_equal(true)
expect(rb).to_equal(true)
expect(dir_exists(a)).to_equal(false)
expect(dir_exists(b)).to_equal(false)
```

</details>

### shell unified signature

#### file_shell, process_ops and io_runtime variants all return ProcessResult

- file_shell, process_ops and io_runtime variants all return ProcessResult
   - Expected: r1.stdout equals `hi`
   - Expected: r2.stdout equals `hi`
   - Expected: r3.stdout equals `hi`
   - Expected: r1.stderr equals `err`
   - Expected: r2.stderr equals `err`
   - Expected: r3.stderr equals `err`
   - Expected: r1.exit_code equals `3`
   - Expected: r2.exit_code equals `3`
   - Expected: r3.exit_code equals `3`
   - Expected: r1.limit_exceeded is false
   - Expected: r3.limit_exceeded is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("file_shell, process_ops and io_runtime variants all return ProcessResult")
val r1 = file_shell_shell("printf hi; printf err >&2; exit 3")
val r2 = process_ops_shell("printf hi; printf err >&2; exit 3")
val r3 = io_runtime_shell("printf hi; printf err >&2; exit 3")
expect(r1.stdout).to_equal("hi")
expect(r2.stdout).to_equal("hi")
expect(r3.stdout).to_equal("hi")
expect(r1.stderr).to_equal("err")
expect(r2.stderr).to_equal("err")
expect(r3.stderr).to_equal("err")
expect(r1.exit_code).to_equal(3)
expect(r2.exit_code).to_equal(3)
expect(r3.exit_code).to_equal(3)
expect(r1.limit_exceeded).to_equal(false)
expect(r3.limit_exceeded).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/io/shell_dir_remove_all_unified_signature_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering dir_remove_all unified signature, shell unified signature.
- dir_remove_all unified signature
- shell unified signature

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `623622abcb2308b999be3460d7bbfb854e19bc9d0facd014decd7e24dddc00e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `623622abcb2308b999be3460d7bbfb854e19bc9d0facd014decd7e24dddc00e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `623622abcb2308b999be3460d7bbfb854e19bc9d0facd014decd7e24dddc00e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/io/shell_dir_remove_all_unified_signature_spec.spl
mirror: doc/06_spec/01_unit/lib/io/shell_dir_remove_all_unified_signature_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/io/shell_dir_remove_all_unified_signature_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/io/shell_dir_remove_all_unified_signature_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/io/shell_dir_remove_all_unified_signature_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/io/shell_dir_remove_all_unified_signature_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dir_ops and io_runtime variants both return bool true on success' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/io/shell_dir_remove_all_unified_signature_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'file_shell, process_ops and io_runtime variants all return ProcessResult' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
