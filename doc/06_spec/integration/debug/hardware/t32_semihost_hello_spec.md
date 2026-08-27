# T32 Semihost Hello Specification

> Tests covering T32 semihost hello-world runner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Semihost Hello Specification

## Scenarios

### T32 semihost hello-world runner

#### ships the runner script

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ships the runner script
   - Expected: rt_file_exists("scripts/t32_semihost_hello.shs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ships the runner script")
expect(rt_file_exists("scripts/t32_semihost_hello.shs")).to_equal(true)
```

</details>

#### reuses the shared STM semihost smoke fixture

- reuses the shared STM semihost smoke fixture
   - Expected: rt_file_exists("test/fixtures/baremetal/stm_semihost_smoke.s") is true
   - Expected: rt_file_exists("test/fixtures/baremetal/stm_semihost_smoke.ld") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reuses the shared STM semihost smoke fixture")
expect(rt_file_exists("test/fixtures/baremetal/stm_semihost_smoke.s")).to_equal(true)
expect(rt_file_exists("test/fixtures/baremetal/stm_semihost_smoke.ld")).to_equal(true)
```

</details>

#### runner help documents board and build-only options

- runner help documents board and build-only options


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runner help documents board and build-only options")
val output = shell("scripts/t32_semihost_hello.shs --help 2>&1")
expect(output).to_contain("--board")
expect(output).to_contain("--build-only")
expect(output).to_contain("stm32wb")
expect(output).to_contain("stm32h7")
```

</details>

#### build-only mode emits the STM smoke ELF

- build-only mode emits the STM smoke ELF


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("build-only mode emits the STM smoke ELF")
val output = shell("scripts/t32_semihost_hello.shs --build-only 2>&1")
expect(output).to_contain("built ELF:")
expect(output).to_contain("stm_semihost_smoke")
```

</details>

#### documents the expected semihost marker

- documents the expected semihost marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("documents the expected semihost marker")
val output = shell("sed -n '1,200p' scripts/t32_semihost_hello.shs")
expect(output).to_contain("simple-stm-smoke")
expect(output).to_contain("WinPrint.AREA MCP_OUT")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/integration/debug/hardware/t32_semihost_hello_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 semihost hello-world runner.
- T32 semihost hello-world runner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e5e8ce483226a69795a52819a24fab5dde668136ddad8820dd7a68a08779de0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e5e8ce483226a69795a52819a24fab5dde668136ddad8820dd7a68a08779de0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e5e8ce483226a69795a52819a24fab5dde668136ddad8820dd7a68a08779de0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/debug/hardware/t32_semihost_hello_spec.spl
mirror: doc/06_spec/integration/debug/hardware/t32_semihost_hello_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/debug/hardware/t32_semihost_hello_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/debug/hardware/t32_semihost_hello_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/debug/hardware/t32_semihost_hello_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships the runner script' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/debug/hardware/t32_semihost_hello_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses the shared STM semihost smoke fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/debug/hardware/t32_semihost_hello_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runner help documents board and build-only options' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
