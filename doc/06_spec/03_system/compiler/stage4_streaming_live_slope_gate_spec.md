# Stage4 Streaming Live Slope Gate Specification

> Tests covering Stage4 streaming live-slope gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage4 Streaming Live Slope Gate Specification

## Scenarios

### Stage4 streaming live-slope gate

#### should run only the exact experimental low-memory path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should run only the exact experimental low-memory path
- Inspect the Stage4 admission environment


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run only the exact experimental low-memory path")
step("Inspect the Stage4 admission environment")
val source = file_read(RUNNER)
expect(source).to_contain("SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE4=1")
expect(source).to_contain("SIMPLE_BOOTSTRAP_LOW_MEMORY=1 SIMPLE_STAGE4_STREAMING_SURFACES=1 SIMPLE_NATIVE_ARENA_DECLS=1")
expect(source).to_contain("SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1 SIMPLE_COMPILER_PHASE_PROFILE=1")
expect(source).to_contain("SIMPLE_NO_STUB_FALLBACK=1")
expect(source).to_contain("--entry-closure --low-memory --threads 1")
```

</details>

#### should reject seed and failed compiler executions

- should reject seed and failed compiler executions
- Inspect fail-closed compiler execution handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject seed and failed compiler executions")
step("Inspect fail-closed compiler execution handling")
val source = file_read(RUNNER)
expect(source).to_contain("Rust bootstrap seed")
expect(source).to_contain("error=selfhost_binary_required")
expect(source).to_contain("timeout -k 5s")
expect(source).to_contain("error=timed_out_after_${{TIME_MAX_S}}s")
expect(source).to_contain("error=native_build_failed:$status")
expect(source).to_contain("error=stale_flat_ast_index")
```

</details>

#### should bind the compiler binary to current source provenance

- should bind the compiler binary to current source provenance
- Inspect binary and source attestation checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind the compiler binary to current source provenance")
step("Inspect binary and source attestation checks")
val source = file_read(RUNNER)
val producer = file_read(PRODUCER)
val provenance = file_read(PROVENANCE)
expect(producer).to_contain("no provenance-verified compiler for Stage 4")
expect(producer).to_contain("SIMPLE_BOOTSTRAP_LOW_MEMORY=1")
expect(producer).to_contain("SIMPLE_STAGE4_STREAMING_SURFACES=1")
expect(producer).to_contain("SIMPLE_NATIVE_ARENA_DECLS=1")
expect(producer).to_contain("stage4_write_candidate_provenance")
expect(producer).to_contain("stage4-essential-tools-smoke")
expect(source).to_contain("stage4_verify_candidate_provenance")
expect(provenance).to_contain("bootstrap_stage3_verify_manifest")
expect(provenance).to_contain("artifact_kind=pure-simple-full-cli")
expect(provenance).to_contain("build_log_sha256")
expect(provenance).to_contain("essential_tools_log_sha256")
expect(provenance).to_contain("bootstrap_essential_tools_smoke=true")
expect(provenance).to_contain("examples/10_tooling")
expect(provenance).to_contain("directory symlink escapes owned roots")
```

</details>

#### should require one release marker per physical source

- should require one release marker per physical source
- Inspect per-source release receipt validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require one release marker per physical source")
step("Inspect per-source release receipt validation")
val source = file_read(RUNNER)
expect(source).to_contain("phase2:surface:file:released")
expect(source).to_contain("/^path=/")
expect(source).to_contain("path != root \"/mod\" file_index \".spl\"")
expect(source).to_contain("/^seq=[0-9]+$/")
expect(source).to_contain("surface_release_marker_count:$marker_count expected:$FILE_COUNT")
expect(source).to_contain("surface_release_marker_invalid")
expect(source).to_contain("stage4_parse_memory_multifile_surface_release_markers=$marker_count")
```

</details>

#### should fail closed on registry slope and RSS ceilings

- should fail closed on registry slope and RSS ceilings
- Inspect live registry and RSS ceilings


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail closed on registry slope and RSS ceilings")
step("Inspect live registry and RSS ceilings")
val source = file_read(RUNNER)
expect(source).to_contain("STAGE4_PARSE_MEM_MULTI_REGISTRY_AVG_GROWTH_MAX")
expect(source).to_contain("STAGE4_PARSE_MEM_MULTI_REGISTRY_STEP_GROWTH_MAX")
expect(source).to_contain("registry_average_growth:$registry_average_growth exceeds:$REGISTRY_AVG_GROWTH_MAX")
expect(source).to_contain("registry_max_step_growth:$registry_max_step_growth exceeds:$REGISTRY_STEP_GROWTH_MAX")
expect(source).to_contain("peak_rss_kib:$max_rss_kib exceeds ceiling $RSS_MAX_KIB")
expect(source).to_contain("stage4_parse_memory_multifile_binary_sha256=")
expect(source).to_contain("stage4_parse_memory_multifile_status=pass")
```

</details>

#### should execute positive and negative marker fixtures

- should execute positive and negative marker fixtures
- Run the bounded gate self-test
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should execute positive and negative marker fixtures")
step("Run the bounded gate self-test")
val (stdout, stderr, code) = process_run_timeout("/bin/sh", [RUNNER, "--self-test"], 120000)
expect(code).to_equal(0)
expect(stdout + stderr).to_contain("STATUS: PASS stage4-streaming-live-slope self-test")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Stage4 streaming live-slope gate.
- Stage4 streaming live-slope gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `e21b781ae5041ce2cc01efda0cba8aa978d6b254583161da6e0785f04e3ba993`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e21b781ae5041ce2cc01efda0cba8aa978d6b254583161da6e0785f04e3ba993`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e21b781ae5041ce2cc01efda0cba8aa978d6b254583161da6e0785f04e3ba993`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl
mirror: doc/06_spec/03_system/compiler/stage4_streaming_live_slope_gate_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/stage4_streaming_live_slope_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/stage4_streaming_live_slope_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl:17:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should run only the exact experimental low-memory path' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should run only the exact experimental low-memory path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject seed and failed compiler executions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject seed and failed compiler executions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind the compiler binary to current source provenance' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bind the compiler binary to current source provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require one release marker per physical source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl:75:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed on registry slope and RSS ceilings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/compiler/stage4_streaming_live_slope_gate_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should execute positive and negative marker fixtures' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
