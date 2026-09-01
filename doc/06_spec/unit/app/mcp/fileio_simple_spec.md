# Fileio Simple Specification

> Tests covering FileIO Simple - Protection Rules, FileIO Simple - Handlers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fileio Simple Specification

## Scenarios

### FileIO Simple - Protection Rules

#### protects critical files

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- protects critical files
   - Expected: check_protection("CLAUDE.md", "read") equals `ALLOWED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("protects critical files")
expect(check_protection("CLAUDE.md", "write")).to_contain("DENIED")
expect(check_protection("CLAUDE.md", "read")).to_equal("ALLOWED")
```

</details>

#### redirects test files and shell scripts

- redirects test files and shell scripts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("redirects test files and shell scripts")
expect(check_protection("test_file.txt", "write")).to_contain("REDIRECT")
expect(check_protection("mcp_test_output.txt", "write")).to_contain("REDIRECT")
expect(check_protection("script.sh", "write")).to_contain("REDIRECT")
```

</details>

#### denies version control and lock files

- denies version control and lock files


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies version control and lock files")
expect(check_protection(".git/config", "write")).to_contain("DENIED")
expect(check_protection(".jj/abc", "write")).to_contain("DENIED")
expect(check_protection("cache.lock", "write")).to_contain("DENIED")
```

</details>

#### requires atomic writes for sdn

- requires atomic writes for sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires atomic writes for sdn")
expect(check_protection("data.sdn", "write")).to_contain("ATOMIC")
```

</details>

#### allows build and tmp directories

- allows build and tmp directories
   - Expected: check_protection("build/output.txt", "write") equals `ALLOWED`
   - Expected: check_protection("tmp/output.txt", "write") equals `ALLOWED`
   - Expected: check_protection("tmp/fileio_temp/output.txt", "write") equals `ALLOWED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows build and tmp directories")
expect(check_protection("build/output.txt", "write")).to_equal("ALLOWED")
expect(check_protection("tmp/output.txt", "write")).to_equal("ALLOWED")
expect(check_protection("tmp/fileio_temp/output.txt", "write")).to_equal("ALLOWED")
```

</details>

#### denies root-level files by default

- denies root-level files by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies root-level files by default")
expect(check_protection("root.txt", "write")).to_contain("DENIED")
```

</details>

#### allows subdirectories by default

- allows subdirectories by default
   - Expected: check_protection("src/file.txt", "write") equals `ALLOWED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows subdirectories by default")
expect(check_protection("src/file.txt", "write")).to_equal("ALLOWED")
```

</details>

### FileIO Simple - Handlers

#### handles safe_write in each mode

- handles safe_write in each mode
   - Expected: allowed.starts_with("OK:" ) is true
   - Expected: denied.starts_with("ERROR:" ) is true
   - Expected: atomic contains `Atomic write required`
   - Expected: comparison.status equals `EvidenceStatus.passed`
   - Expected: redirected contains `temp`
   - Expected: file_exists("tmp/fileio_temp/test_file.txt") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles safe_write in each mode")
shell("mkdir -p tmp/fileio_temp")
val allowed = handle_safe_write("tmp/mcp_simple_allowed.txt", "ok")
expect(allowed.starts_with("OK:" )).to_equal(true)
val denied = handle_safe_write("CLAUDE.md", "x")
expect(denied.starts_with("ERROR:" )).to_equal(true)
val atomic = handle_safe_write("data.sdn", "x")
expect(atomic.contains("Atomic write required")).to_equal(true)

val capture = UntypedCapture(label: "fileio-simple-atomic-write-response", raw_value: atomic, source_kind: "log_line")
val evidence = untyped_capture_to_canonical(capture, "fileio_simple_spec/atomic-write-response")
val comparison = compare_evidence(evidence, oracle_spec("fileio_simple_spec/atomic-write-response", [
    check_exact("value", "ERROR: Atomic write required (use safe_atomic_write)")
]))
expect(comparison.status).to_equal(EvidenceStatus.passed)
val redirected = handle_safe_write("test_file.txt", "x")
expect(redirected.contains("temp" )).to_equal(true)
expect(file_exists("tmp/fileio_temp/test_file.txt")).to_equal(true)
```

</details>

#### handles safe_read

- handles safe_read
   - Expected: ok.starts_with("OK:" ) is true
   - Expected: missing contains `File not found`
   - Expected: denied.starts_with("ERROR:" ) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles safe_read")
val path = "/tmp/mcp_simple_read.txt"
file_write(path, "read")
val ok = handle_safe_read(path)
expect(ok.starts_with("OK:" )).to_equal(true)
val missing = handle_safe_read("/tmp/mcp_simple_missing.txt")
expect(missing.contains("File not found")).to_equal(true)
val denied = handle_safe_read("README.md")
expect(denied.starts_with("ERROR:" )).to_equal(true)
```

</details>

#### handles check_protection handler

- handles check_protection handler
   - Expected: resp contains `PROTECTION:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles check_protection handler")
val resp = handle_check_protection("data.sdn")
expect(resp.contains("PROTECTION:" )).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp/fileio_simple_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering FileIO Simple - Protection Rules, FileIO Simple - Handlers.
- FileIO Simple - Protection Rules
- FileIO Simple - Handlers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `451474c07f65d253c5a430929fd9c42ea783348320297552648f09063a575355`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `451474c07f65d253c5a430929fd9c42ea783348320297552648f09063a575355`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `451474c07f65d253c5a430929fd9c42ea783348320297552648f09063a575355`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp/fileio_simple_spec.spl
mirror: doc/06_spec/unit/app/mcp/fileio_simple_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp/fileio_simple_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp/fileio_simple_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp/fileio_simple_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'protects critical files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp/fileio_simple_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'redirects test files and shell scripts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp/fileio_simple_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies version control and lock files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
