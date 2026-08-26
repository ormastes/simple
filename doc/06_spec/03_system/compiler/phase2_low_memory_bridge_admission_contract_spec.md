# Phase2 Low Memory Bridge Admission Contract Specification

> Tests covering Wave-0 low-memory bridge admission preparation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Phase2 Low Memory Bridge Admission Contract Specification

## Scenarios

### Wave-0 low-memory bridge admission preparation

#### requires all three exact opt-ins in the canonical bootstrap API

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires all three exact opt-ins in the canonical bootstrap API
   - Expected: source does not contain `options.low_memory = true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires all three exact opt-ins in the canonical bootstrap API")
val source = file_read(API)
val config = file_read(CONFIG)
expect(source).to_contain("pub fn bootstrap_low_memory_requested() -> bool:")
expect(source).to_contain("bootstrap_low_memory_opt_ins_requested(")
expect(source).to_contain("env_get(\"SIMPLE_BOOTSTRAP\")")
expect(source).to_contain("env_get(\"SIMPLE_BOOTSTRAP_STAGE4\")")
expect(source).to_contain("env_get(\"SIMPLE_BOOTSTRAP_LOW_MEMORY\")")
expect(config).to_contain("bootstrap == \"1\" and stage4 == \"1\" and low_memory == \"1\"")
expect(source).to_contain("options.low_memory = bootstrap_low_memory_requested()")
expect(source.contains("options.low_memory = true")).to_equal(false)
```

</details>

#### tracks one focused full-driver bridge and live probe

- tracks one focused full-driver bridge and live probe
   - Expected: bridge does not contain `rt_native_build`
   - Expected: probe does not contain `rt_native_build`
   - Expected: bridge does not contain `bootstrap-stage4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks one focused full-driver bridge and live probe")
val bridge = file_read(BRIDGE)
val probe = file_read(PROBE)
expect(bridge).to_contain("simple-wave0-low-memory-bridge 1")
expect(bridge).to_contain("options.low_memory = bootstrap_low_memory_requested()")
expect(bridge).to_contain("compiler_driver_run_compile(compiler_driver_create(options))")
expect(bridge).to_contain("build-probe")
expect(probe).to_contain("options.mode = CompileMode.Check")
expect(probe).to_contain("options.low_memory = enabled")
expect(probe).to_contain("bootstrap_low_memory_probe_capsule_first_free={{first_free}}")
expect(probe).to_contain("bootstrap_low_memory_probe_capsule_alias_refusal={{alias_refusal}}")
expect(bridge.contains("rt_native_build")).to_equal(false)
expect(probe.contains("rt_native_build")).to_equal(false)
expect(bridge.contains("bootstrap-stage4")).to_equal(false)
```

</details>

#### binds the current driver trace and accepted runtime prerequisite

- binds the current driver trace and accepted runtime prerequisite


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds the current driver trace and accepted runtime prerequisite")
val driver = file_read(DRIVER)
val report = file_read(CAPSULE_REPORT)
val start_pos = driver.index_of("phase2:source_reclaim:start low_memory=true")
val reclaim_pos = driver.index_of("val reclaimed_sources = self.ctx.reclaim_source_contents()")
val done_pos = driver.index_of("phase2:source_reclaim:done reclaimed={{reclaimed_sources}}")
expect(start_pos).to_be_greater_than(0)
expect(reclaim_pos).to_be_greater_than(start_pos)
expect(done_pos).to_be_greater_than(reclaim_pos)
expect(report).to_contain("Runtime capsule: ACCEPT. Compiler Wave 0: NOT ADMITTED.")
expect(report).to_contain("rt_string_free")
expect(report).to_contain("runtime_native.o")
```

</details>

#### keeps execution evidence fail closed until a reviewed runner exists

- keeps execution evidence fail closed until a reviewed runner exists
   - Expected: bridge does not contain `SIMPLE_NO_STUB_FALLBACK`
   - Expected: probe does not contain `SIMPLE_RUNTIME_PATH`
   - Expected: bridge does not contain `candidate_frontend_admission`
   - Expected: probe does not contain `native_cli_mode_transport_regression_spec`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps execution evidence fail closed until a reviewed runner exists")
val bridge = file_read(BRIDGE)
val probe = file_read(PROBE)
expect(bridge.contains("SIMPLE_NO_STUB_FALLBACK")).to_equal(false)
expect(probe.contains("SIMPLE_RUNTIME_PATH")).to_equal(false)
expect(bridge.contains("candidate_frontend_admission")).to_equal(false)
expect(probe.contains("native_cli_mode_transport_regression_spec")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wave-0 low-memory bridge admission preparation.
- Wave-0 low-memory bridge admission preparation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `16c1ccd8028a3741d20e9ebaf50aaa954b573b82cefa87c24649f2d4877166b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `16c1ccd8028a3741d20e9ebaf50aaa954b573b82cefa87c24649f2d4877166b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `16c1ccd8028a3741d20e9ebaf50aaa954b573b82cefa87c24649f2d4877166b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.spl
mirror: doc/06_spec/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires all three exact opt-ins in the canonical bootstrap API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks one focused full-driver bridge and live probe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the current driver trace and accepted runtime prerequisite' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
