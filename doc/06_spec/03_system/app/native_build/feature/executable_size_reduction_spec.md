# Executable Size Reduction Specification

> Tests covering executable size reduction, REQ-001 through REQ-004: native runtime archive retention, REQ-005 and REQ-006: release size guardrails, REQ-007 through REQ-010: loader dependency closure, REQ-011 through REQ-014: native binary dependency audit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Executable Size Reduction Specification

## Scenarios

### executable size reduction

### REQ-001 through REQ-004: native runtime archive retention

#### uses explicit runtime roots instead of default ELF whole-archive linking
#### keeps a diagnostic fallback for legacy runtime whole-archive linking

- keeps a diagnostic fallback for legacy runtime whole-archive linking
   - Expected: fallback_env equals `SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps a diagnostic fallback for legacy runtime whole-archive linking")
val fallback_env = "SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE"
expect(fallback_env).to_equal("SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE")
```

</details>

### REQ-005 and REQ-006: release size guardrails

#### strips packaged native MCP binaries

- strips packaged native MCP binaries
   - Expected: package_flag equals `--strip`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("strips packaged native MCP binaries")
val package_flag = "--strip"
expect(package_flag).to_equal("--strip")
```

</details>

#### checks release executable and runtime archive budgets

- checks release executable and runtime archive budgets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks release executable and runtime archive budgets")
val script = "scripts/check/check-executable-size-budgets.shs"
expect(script).to_end_with("check-executable-size-budgets.shs")
```

</details>

### REQ-007 through REQ-010: loader dependency closure

#### owns the runtime symbol ABI in a dedicated crate

- owns the runtime symbol ABI in a dedicated crate
   - Expected: abi_crate equals `simple-runtime-abi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("owns the runtime symbol ABI in a dedicated crate")
val abi_crate = "simple-runtime-abi"
expect(abi_crate).to_equal("simple-runtime-abi")
```

</details>

#### audits loader dependency closure with a dedicated script

- audits loader dependency closure with a dedicated script


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("audits loader dependency closure with a dedicated script")
val script = "scripts/check/check-loader-dependency-closure.shs"
expect(script).to_end_with("check-loader-dependency-closure.shs")
```

</details>

#### keeps simple-native-loader off simple-runtime normal deps

- keeps simple-native-loader off simple-runtime normal deps


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps simple-native-loader off simple-runtime normal deps")
val runtime_edge = "simple-native-loader -> simple-runtime"
expect(runtime_edge).to_contain("simple-runtime")
```

</details>

### REQ-011 through REQ-014: native binary dependency audit

#### audits native binary dependency closure with a dedicated script

- audits native binary dependency closure with a dedicated script


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("audits native binary dependency closure with a dedicated script")
val script = "scripts/check/check-native-binary-dependency-closure.shs"
expect(script).to_end_with("check-native-binary-dependency-closure.shs")
```

</details>

#### tracks the CLI root through simple-driver

- tracks the CLI root through simple-driver
   - Expected: cli_root equals `simple-driver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks the CLI root through simple-driver")
val cli_root = "simple-driver"
expect(cli_root).to_equal("simple-driver")
```

</details>

#### surfaces simple-native-all overreach into simple-driver

- surfaces simple-native-all overreach into simple-driver


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("surfaces simple-native-all overreach into simple-driver")
val edge = "simple-native-all -> simple-driver"
expect(edge).to_contain("simple-driver")
```

</details>

#### keeps stale external jj crate deps out of simple-driver

- keeps stale external jj crate deps out of simple-driver


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps stale external jj crate deps out of simple-driver")
val forbidden = "jj-lib,jj-cli,hostname"
expect(forbidden).to_contain("hostname")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/native_build/feature/executable_size_reduction_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering executable size reduction, REQ-001 through REQ-004: native runtime archive retention, REQ-005 and REQ-006: release size guardrails, REQ-007 through REQ-010: loader dependency closure, REQ-011 through REQ-014: native binary dependency audit.
- executable size reduction
- REQ-001 through REQ-004: native runtime archive retention
- REQ-005 and REQ-006: release size guardrails
- REQ-007 through REQ-010: loader dependency closure
- REQ-011 through REQ-014: native binary dependency audit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-004:`
- `REQ-001`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-010`
- `REQ-011`
- `REQ-014`
- `REQ-006:`
- `REQ-010:`
- `REQ-014:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dea97207aff01270028d5e338fa3f4897efa76ea602ba389fcc19d96af5fdb17`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dea97207aff01270028d5e338fa3f4897efa76ea602ba389fcc19d96af5fdb17`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dea97207aff01270028d5e338fa3f4897efa76ea602ba389fcc19d96af5fdb17`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/native_build/feature/executable_size_reduction_spec.spl
mirror: doc/06_spec/03_system/app/native_build/feature/executable_size_reduction_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=90 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/03_system/app/native_build/feature/executable_size_reduction_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/native_build/feature/executable_size_reduction_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/native_build/feature/executable_size_reduction_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 8 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/native_build/feature/executable_size_reduction_spec.spl:12:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'uses explicit runtime roots instead of default ELF whole-archive linking' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/native_build/feature/executable_size_reduction_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a diagnostic fallback for legacy runtime whole-archive linking' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/native_build/feature/executable_size_reduction_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strips packaged native MCP binaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/native_build/feature/executable_size_reduction_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks release executable and runtime archive budgets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
