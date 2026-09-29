# Lint Cli Contract Specification

> Tests covering simple lint CLI contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lint Cli Contract Specification

## Scenarios

### simple lint CLI contract

#### defers the theme package outside theme lint targets

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defers the theme package outside theme lint targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defers the theme package outside theme lint targets")
val split_dir = "src/compiler/90.tools/lint/_LintMain/"
val split_files = [
    "config_and_model.spl",
    "entry_and_fixes.spl",
    "lint_checks.spl",
    "traceability_and_assertions.spl",
]
for file in split_files:
    expect(file_read(split_dir + file).contains(
        "use nogc_sync_mut.ui.theme_package")).to_equal(false)
expect(file_read(split_dir + "lint_checks.spl")).to_contain(
    "use lazy nogc_sync_mut.ui.theme_package.{validate_default_theme_package}")
```

</details>

#### loads the theme validator for a theme lint target

- loads the theme validator for a theme lint target
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loads the theme validator for a theme lint target")
val (stdout, stderr, code) = run_lint(["config/themes/theme.sdn"])
expect(code).to_equal(0)
expect(stdout).to_contain("Lint passed: all files clean")
```

</details>

#### exits 0 and reports clean on a violation-free file

- exits 0 and reports clean on a violation-free file
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exits 0 and reports clean on a violation-free file")
val (stdout, stderr, code) = run_lint(["test/fixtures/lint/clean.spl"])
expect(code).to_equal(0)
expect(stdout).to_contain("Lint passed: all files clean")
```

</details>

#### exits nonzero and names real violations

- exits nonzero and names real violations
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exits nonzero and names real violations")
val (stdout, stderr, code) = run_lint(["test/fixtures/lint/dirty.spl"])
expect(code).to_equal(1)
expect(stdout).to_contain("W001")
expect(stdout).to_contain("D001")
expect(stdout).to_contain("PARSE001")
expect(stdout).to_contain("Lint failed in 1 file(s)")
```

</details>

#### reports an unparseable file as NOT LINTED, loudly and countably

- reports an unparseable file as NOT LINTED, loudly and countably
   - Expected: code equals `1`
   - Expected: stdout does not contain `Lint passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports an unparseable file as NOT LINTED, loudly and countably")
# A file the parse gate rejects has been analysed LESS than a clean
# file, not more: every AST-based lint is skipped for it. Reporting it
# as one ordinary error made it read as checked. The run must name the
# file, count the skips separately, and exit nonzero.
val (stdout, stderr, code) = run_lint(["test/fixtures/lint/dirty.spl"])
expect(code).to_equal(1)
expect(stdout).to_contain("PARSE001")
expect(stdout).to_contain("NOT LINTED: test/fixtures/lint/dirty.spl")
expect(stdout).to_contain("NOT LINTED: 1 file(s) could not be parsed and were never analysed")
expect(stdout.contains("Lint passed")).to_equal(false)
```

</details>

#### never summarises a run with a skipped file as passed

- never summarises a run with a skipped file as passed
   - Expected: code equals `1`
   - Expected: stdout does not contain `Lint passed: all files clean`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("never summarises a run with a skipped file as passed")
val (stdout, stderr, code) = run_lint(["test/fixtures/lint/dirty.spl", "test/fixtures/lint/clean.spl"])
expect(code).to_equal(1)
expect(stdout).to_contain("NOT LINTED: 1 file(s) could not be parsed and were never analysed")
expect(stdout.contains("Lint passed: all files clean")).to_equal(false)
```

</details>

#### counts skipped files in the JSON summary

- counts skipped files in the JSON summary
   - Expected: code equals `1`
   - Expected: stdout does not contain `NOT LINTED: 1 file(s)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("counts skipped files in the JSON summary")
val (stdout, stderr, code) = run_lint(["test/fixtures/lint/dirty.spl", "--json"])
expect(code).to_equal(1)
expect(stdout).to_contain("\"type\":\"lint-not-linted\"")
expect(stdout).to_contain("\"not_linted\":true")
expect(stdout).to_contain("\"not_linted_files\":1")
# The human-readable summary banner must stay out of JSON mode; the
# phrase still appears inside the PARSE001 diagnostic message itself.
expect(stdout.contains("NOT LINTED: 1 file(s)")).to_equal(false)
expect_json_lines(stdout)
```

</details>

#### reports zero skipped files on a clean run

- reports zero skipped files on a clean run
   - Expected: code equals `0`
   - Expected: stdout does not contain `lint-not-linted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports zero skipped files on a clean run")
val (stdout, stderr, code) = run_lint(["test/fixtures/lint/clean.spl", "--json"])
expect(code).to_equal(0)
expect(stdout).to_contain("\"not_linted_files\":0")
expect(stdout.contains("lint-not-linted")).to_equal(false)
expect_json_lines(stdout)
```

</details>

#### deduplicates overlapping directory and file targets

- deduplicates overlapping directory and file targets
   - Expected: code equals `1`
   - Expected: stdout.split("warning[W001]").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deduplicates overlapping directory and file targets")
val (stdout, stderr, code) = run_lint([
    "./test/fixtures/pure_simple_tooling/lint_directory",
    "test/fixtures/pure_simple_tooling/lint_directory/nested/dirty.spl"
])
expect(code).to_equal(1)
expect(stdout.split("warning[W001]").len()).to_equal(2)
expect(stdout).to_contain("Lint failed in 1 file(s)")
```

</details>

#### emits JSON Lines without human summaries

- emits JSON Lines without human summaries
   - Expected: code equals `1`
   - Expected: stdout does not contain `Lint failed in`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits JSON Lines without human summaries")
val (stdout, stderr, code) = run_lint(["test/fixtures/lint/dirty.spl", "--json"])
expect(code).to_equal(1)
expect(stdout).to_contain("\"type\":\"lint-diagnostic\"")
expect(stdout).to_contain("\"type\":\"lint-summary\",\"status\":\"failed\"")
expect(stdout.contains("Lint failed in")).to_equal(false)
expect_json_lines(stdout)
```

</details>

#### emits one failed summary when an input file is missing

- emits one failed summary when an input file is missing
   - Expected: code equals `1`
   - Expected: stdout.split("\"type\":\"lint-error\"").len() equals `2`
   - Expected: stdout.split("\"type\":\"lint-summary\"").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("emits one failed summary when an input file is missing")
val missing = "test/fixtures/lint/definitely_missing.spl"
val (stdout, stderr, code) = run_lint([missing, "./" + missing, "--json"])
expect(code).to_equal(1)
expect(stdout).to_contain("\"type\":\"lint-error\"")
expect(stdout.split("\"type\":\"lint-error\"").len()).to_equal(2)
expect(stdout).to_contain("\"type\":\"lint-summary\",\"status\":\"failed\",\"failed_files\":1")
expect(stdout.split("\"type\":\"lint-summary\"").len()).to_equal(2)
expect_json_lines(stdout)
```

</details>

#### recursively expands a relative directory target

- recursively expands a relative directory target
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recursively expands a relative directory target")
val (stdout, stderr, code) = run_lint(["test/fixtures/pure_simple_tooling/lint_directory"])
expect(code).to_equal(1)
expect(stdout).to_contain("W001")
expect(stdout).to_contain("D001")
expect(stdout).to_contain("Lint failed in 1 file(s)")
```

</details>

#### fails explicitly when a directory contains no Simple sources

- fails explicitly when a directory contains no Simple sources
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails explicitly when a directory contains no Simple sources")
val (stdout, stderr, code) = run_lint([
    "test/fixtures/pure_simple_tooling/lint_empty",
    "test/fixtures/pure_simple_tooling/lint_empty",
    "--json"
])
expect(code).to_equal(1)
expect(stdout).to_contain("\"type\":\"lint-error\"")
expect(stdout).to_contain("\"message\":\"no Simple source files found\"")
expect(stdout).to_contain("\"type\":\"lint-summary\",\"status\":\"failed\",\"failed_files\":1")
expect_json_lines(stdout)
```

</details>

#### runs fix-dry-run without mutating the input

- runs fix-dry-run without mutating the input
   - Expected: file_atomic_write(fixture, FIX_SOURCE) is true
   - Expected: code equals `0`
   - Expected: file_read(fixture) equals `FIX_SOURCE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs fix-dry-run without mutating the input")
val fixture = fix_fixture("dry_human")
expect(file_atomic_write(fixture, FIX_SOURCE)).to_equal(true)
val (stdout, stderr, code) = run_lint([fixture, "--fix-dry-run"])
expect(code).to_equal(0)
expect(stdout).to_contain("Dry run - would apply")
expect(file_read(fixture)).to_equal(FIX_SOURCE)
file_delete(fixture)
```

</details>

#### keeps JSON fix-dry-run output as JSON Lines

- keeps JSON fix-dry-run output as JSON Lines
   - Expected: file_atomic_write(fixture, FIX_SOURCE) is true
   - Expected: code equals `0`
   - Expected: stdout does not contain `Dry run - would apply`
   - Expected: file_read(fixture) equals `FIX_SOURCE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps JSON fix-dry-run output as JSON Lines")
val fixture = fix_fixture("dry_json")
expect(file_atomic_write(fixture, FIX_SOURCE)).to_equal(true)
val (stdout, stderr, code) = run_lint([fixture, "--json", "--fix-dry-run"])
expect(code).to_equal(0)
expect(stdout).to_contain("\"type\":\"lint-fix-summary\"")
expect(stdout).to_contain("\"mode\":\"dry-run\"")
expect(stdout.contains("Dry run - would apply")).to_equal(false)
expect_json_lines(stdout)
expect(file_read(fixture)).to_equal(FIX_SOURCE)
file_delete(fixture)
```

</details>

#### applies JSON fixes atomically without human output

- applies JSON fixes atomically without human output
   - Expected: file_atomic_write(fixture, FIX_SOURCE) is true
   - Expected: code equals `0`
   - Expected: stdout does not contain `Applied `
   - Expected: file_read(fixture) equals `FIX_EXPECTED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies JSON fixes atomically without human output")
val fixture = fix_fixture("apply_json")
expect(file_atomic_write(fixture, FIX_SOURCE)).to_equal(true)
val (stdout, stderr, code) = run_lint([fixture, "--json", "--fix"])
expect(code).to_equal(0)
expect(stdout).to_contain("\"type\":\"lint-fix-summary\"")
expect(stdout).to_contain("\"mode\":\"applied\"")
expect(stdout.contains("Applied ")).to_equal(false)
expect_json_lines(stdout)
expect(file_read(fixture)).to_equal(FIX_EXPECTED)
file_delete(fixture)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/lint_cli_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple lint CLI contract.
- simple lint CLI contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `11205b1a7983fb1b0f6e8e15fa5d360c8d5d1ce9a7193374376e732f460b2ab6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `11205b1a7983fb1b0f6e8e15fa5d360c8d5d1ce9a7193374376e732f460b2ab6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `11205b1a7983fb1b0f6e8e15fa5d360c8d5d1ce9a7193374376e732f460b2ab6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/lint_cli_contract_spec.spl
mirror: doc/06_spec/03_system/app/lint_cli_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/lint_cli_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/lint_cli_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/lint_cli_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/lint_cli_contract_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defers the theme package outside theme lint targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/lint_cli_contract_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads the theme validator for a theme lint target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/lint_cli_contract_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exits 0 and reports clean on a violation-free file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
