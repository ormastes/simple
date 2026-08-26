# Genuine Import Ownership Specification

> Tests covering genuine import ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Genuine Import Ownership Specification

## Scenarios

### genuine import ownership

#### binds handler compile and check symbols to their leaf owners

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds handler compile and check symbols to their leaf owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binds handler compile and check symbols to their leaf owners")
val source = file_read("src/app/io/_CliCommands/handler_commands.spl")
expect(source).to_contain(r"use compiler.driver.driver_api_core.{interpret_file, check_file}")
expect(source).to_contain(r"use compiler.driver.driver_types.{CompileResult}")
expect(source).to_contain(r"use app.io.cli_compile.{cli_compile}")
```

</details>

#### does not rely on the circular command facade for compile-driver symbols

- does not rely on the circular command facade for compile-driver symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not rely on the circular command facade for compile-driver symbols")
val source = file_read("src/app/io/_CliCommands/handler_commands.spl")
val owner_prefix = source.substring(0, source.find("fn cli_run_i18n"))
expect(owner_prefix).to_contain("use app.io.cli_commands.*")
expect(owner_prefix).to_contain(r"use app.io.cli_compile.{cli_compile}")
expect(owner_prefix).to_contain(r"use compiler.driver.driver_api_core.{interpret_file, check_file}")
```

</details>

#### imports SdnValue at module scope in both db_atomic implementations

- imports SdnValue at module scope in both db_atomic implementations
   - Expected: source does not contain `r"    use std.sdn.{SdnValue}"`
   - Expected: source does not contain `r"use std.sdn.{parse, SdnValue}"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("imports SdnValue at module scope in both db_atomic implementations")
for path in [
    "src/lib/nogc_sync_mut/db_atomic.spl",
    "src/lib/nogc_async_mut/db_atomic.spl"
]:
    val source = file_read(path)
    expect(source).to_contain(r"use std.sdn.{SdnValue}" + "\n")
    expect(source.contains(r"    use std.sdn.{SdnValue}")).to_equal(false)
    expect(source.contains(r"use std.sdn.{parse, SdnValue}")).to_equal(false)
    expect(source).to_contain(r"use std.sdn.{parse}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/genuine_import_ownership_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering genuine import ownership.
- genuine import ownership

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a31801fcf55c89b7b6c097f9dac8c85796731bafbd97b59348d7faaae59979be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a31801fcf55c89b7b6c097f9dac8c85796731bafbd97b59348d7faaae59979be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a31801fcf55c89b7b6c097f9dac8c85796731bafbd97b59348d7faaae59979be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/genuine_import_ownership_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/genuine_import_ownership_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/genuine_import_ownership_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/genuine_import_ownership_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/genuine_import_ownership_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/driver/genuine_import_ownership_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds handler compile and check symbols to their leaf owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/genuine_import_ownership_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not rely on the circular command facade for compile-driver symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/genuine_import_ownership_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports SdnValue at module scope in both db_atomic implementations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
