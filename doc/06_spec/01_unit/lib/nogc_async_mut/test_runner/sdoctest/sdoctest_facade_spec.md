# Sdoctest Facade Specification

> Tests covering nogc_async_mut sdoctest facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdoctest Facade Specification

## Scenarios

### nogc_async_mut sdoctest facade

#### re-exports config parsing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports config parsing
   - Expected: config.default_timeout equals `5000`
   - Expected: config.environments[0].name equals `default`
   - Expected: parsed.default_timeout equals `9000`
   - Expected: parsed.ignore.paths equals `["build/**", "vendor/**"]`
   - Expected: parsed.ignore.tags equals `["slow"]`
   - Expected: parsed.environments[0].name equals `ci`
   - Expected: parsed.environments[0].timeout equals `12000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports config parsing")
val config = default_sdoctest_config()
expect(config.default_timeout).to_equal(5000)
expect(config.environments[0].name).to_equal("default")

val parsed = parse_config_from_text("sdoctest:\n  version: 1\n  default_timeout: 9000\nignore:\n  paths: [\"build/**\", \"vendor/**\"]\n  tags: [\"slow\"]\nenvironments:\n  ci:\n    timeout: 12000\n")
expect(parsed.default_timeout).to_equal(9000)
expect(parsed.ignore.paths).to_equal(["build/**", "vendor/**"])
expect(parsed.ignore.tags).to_equal(["slow"])
expect(parsed.environments[0].name).to_equal("ci")
expect(parsed.environments[0].timeout).to_equal(12000)
```

</details>

#### re-exports extraction and result helpers

- re-exports extraction and result helpers
   - Expected: parsed.0 equals `spl`
   - Expected: parsed.1.len() as i64 equals `2`
   - Expected: block.has_modifier_skip() is true
   - Expected: block.has_modifier_should_fail() is false
   - Expected: block_status_to_str(BlockStatus.Passed) equals `passed`
   - Expected: run.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports extraction and result helpers")
val parsed = parse_fence_line("```spl:skip,tag=fast")
expect(parsed.0).to_equal("spl")
expect(parsed.1.len() as i64).to_equal(2)

val block = SdoctestBlock(source_file: "README.md", line_number: 7, code: "1 + 1", language: "spl", modifiers: [SdoctestModifier.Skip])
expect(block.has_modifier_skip()).to_equal(true)
expect(block.has_modifier_should_fail()).to_equal(false)
expect(block_status_to_str(BlockStatus.Passed)).to_equal("passed")

val run = SdoctestRunResult(files: [], total: 1, passed: 1, failed: 0, skipped: 0, errors: 0, accepted: 0, duration_ms: 1)
expect(run.is_ok()).to_equal(true)
```

</details>

#### re-exports glob helpers

- re-exports glob helpers
   - Expected: glob_match_path("doc/guide/example.md", "doc/**/*.md") is true
   - Expected: glob_match_path("src/main.spl", "doc/**/*.md") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-exports glob helpers")
expect(glob_match_path("doc/guide/example.md", "doc/**/*.md")).to_equal(true)
expect(glob_match_path("src/main.spl", "doc/**/*.md")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut sdoctest facade.
- nogc_async_mut sdoctest facade

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

- Canonical SPipe generation for source `9a668752d1a394a6e1f921e4c0620d88027fd119e4ce6bd5a3a5cb44cb0733f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a668752d1a394a6e1f921e4c0620d88027fd119e4ce6bd5a3a5cb44cb0733f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a668752d1a394a6e1f921e4c0620d88027fd119e4ce6bd5a3a5cb44cb0733f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports config parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports extraction and result helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports glob helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
