# Argv Provider Source Contract Specification

> Tests covering Canonical argv providers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Argv Provider Source Contract Specification

## Scenarios

### Canonical argv providers

#### keeps every pure-Simple argv alias on one store

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps every pure-Simple argv alias on one store


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("keeps every pure-Simple argv alias on one store")
val source = file_read("src/runtime/simple_core/core_process.spl")
expect(source).to_contain("pub fn spl_init_args(argc: i64, argv: i64) -> i64:")
expect(source).to_contain("return rt_set_args(argc, argv)")
expect(source).to_contain("pub fn rt_get_args() -> i64:")
expect(source).to_contain("pub fn sys_get_args() -> i64:")
expect(source).to_contain("return rt_cli_get_args()")
```

</details>

#### publishes and reads SimpleOS argv through canonical weak aliases

- publishes and reads SimpleOS argv through canonical weak aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("publishes and reads SimpleOS argv through canonical weak aliases")
val source = file_read("src/os/libc/simpleos_libc.c")
expect(source).to_contain("__attribute__((weak)) void rt_set_args(int64_t argc, int64_t argv)")
expect(source).to_contain("__attribute__((weak)) void spl_init_args(int argc, char **argv)")
expect(source).to_contain("__attribute__((weak)) int64_t rt_cli_get_args(void)")
expect(source).to_contain("__attribute__((weak)) int64_t rt_get_args(void)")
expect(source).to_contain("__attribute__((weak)) int64_t sys_get_args(void)")
expect(source).to_contain("return rt_cli_get_args();")
expect(source.contains("simpleos_runtime_set_args")).to_be(false)
expect(source.contains("simpleos_runtime_cli_get_args")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/argv_provider_source_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Canonical argv providers.
- Canonical argv providers

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

- `REQ-SSPEC-RUNTIME`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c833d6ac5f82b6ecd412d9c83f6a7cd75ec9b5d84e596fe3924531183d31d59a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c833d6ac5f82b6ecd412d9c83f6a7cd75ec9b5d84e596fe3924531183d31d59a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c833d6ac5f82b6ecd412d9c83f6a7cd75ec9b5d84e596fe3924531183d31d59a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/runtime/argv_provider_source_contract_spec.spl
mirror: doc/06_spec/01_unit/runtime/argv_provider_source_contract_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/runtime/argv_provider_source_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/argv_provider_source_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/argv_provider_source_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/runtime/argv_provider_source_contract_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every pure-Simple argv alias on one store' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/argv_provider_source_contract_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes and reads SimpleOS argv through canonical weak aliases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
