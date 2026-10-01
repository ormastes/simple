# Rv64 Wm Boot Resources Specification

> Tests covering RV64 WM boot resource admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64 Wm Boot Resources Specification

## Scenarios

### RV64 WM boot resource admission

#### accepts only canonical 32-bit packed scanout metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts only canonical 32-bit packed scanout metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts only canonical 32-bit packed scanout metadata")
expect(rv64_wm_scanout_metadata_valid(0x1000u64, 800u32, 600u32, 3200u32, 32u32)).to_be(true)
expect(rv64_wm_scanout_metadata_valid(0u64, 800u32, 600u32, 3200u32, 32u32)).to_be(false)
expect(rv64_wm_scanout_metadata_valid(0x1000u64, 800u32, 600u32, 800u32, 32u32)).to_be(false)
```

</details>

#### requires one correlated process-owned content frame

- requires one correlated process-owned content frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("requires one correlated process-owned content frame")
expect(rv64_wm_snapshot_facts_ready(41u64, 41u64, 1, true, true, 1, 7)).to_be(true)
expect(rv64_wm_snapshot_facts_ready(41u64, 42u64, 1, true, true, 1, 7)).to_be(false)
expect(rv64_wm_snapshot_facts_ready(41u64, 41u64, 1, true, true, 0, 7)).to_be(false)
expect(rv64_wm_snapshot_facts_ready(41u64, 41u64, 0, true, true, 1, 7)).to_be(false)
```

</details>

#### freezes the source-proven path and bounded pump budget

- freezes the source-proven path and bounded pump budget
   - Expected: RV64_WM_BOOT_BINARY_PATH equals `/sys/apps/browser_demo.smf`
   - Expected: RV64_WM_BOOT_MAX_PUMP_ATTEMPTS equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("freezes the source-proven path and bounded pump budget")
expect(RV64_WM_BOOT_BINARY_PATH).to_equal("/sys/apps/browser_demo.smf")
expect(RV64_WM_BOOT_MAX_PUMP_ATTEMPTS).to_equal(64)
```

</details>

#### keeps the serial entry on production resources and one module init

- keeps the serial entry on production resources and one module init
   - Expected: source.index_of("wm_producer.present_snapshot(executor, snapshot)") equals `source.last_index_of("wm_producer.present_snapshot(executor, snapshot)")`
   - Expected: source.index_of("gate.observe_wm(wm_result)") equals `source.last_index_of("gate.observe_wm(wm_result)")`
   - Expected: source.index_of("wm_producer.pump_one_published_action(shell)") equals `source.last_index_of("wm_producer.pump_one_published_action(shell)")`
   - Expected: source.index_of(module_init) equals `source.last_index_of(module_init)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps the serial entry on production resources and one module init")
val source = file_read("examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl")
expect(source).to_contain("if not launcher_path_exists(RV64_WM_BOOT_BINARY_PATH):")
expect(source).to_contain("Rv64ProductionWmProducer.launch(")
expect(source).to_contain("wm_producer.pump_one_published_action(shell)")
expect(source).to_contain("wm_producer.present_snapshot(executor, snapshot)")
expect(source).to_contain("if not riscv64_display_present():")
expect(source).to_contain("var wm_gate_complete = false")
expect(source).to_contain("var wm_last_scene_revision: i64 = 0")
expect(source).to_contain("var wm_last_taskbar_revision: i64 = 0")
expect(source).to_contain("var wm_last_scanout_generation: i64 = 0")
expect(source).to_contain("if not wm_gate_complete:")
expect(source).to_contain("else:\n                    val producer_live = rv64_wm_process_liveness(wm_producer.process_id)")
expect(source).to_contain("wm_gate_complete = true")
expect(source).to_contain("val terminal_verdict = gate.verdict()")
expect(source).to_contain("if terminal_verdict != \"PASS\":")
expect(source).to_contain("verdict=\" + terminal_verdict + \"; sshd remains accepting")
expect(source.contains("verdict=PASS; sshd remains accepting")).to_be(false)
expect(source).to_contain("not snapshot_ready and wm_pump_attempts >= RV64_WM_BOOT_MAX_PUMP_ATTEMPTS")
expect(source.contains("gate.observe_wm(wm_result)\n                    return")).to_be(false)
expect(source.index_of("wm_producer.present_snapshot(executor, snapshot)")).to_equal(source.last_index_of("wm_producer.present_snapshot(executor, snapshot)"))
expect(source.index_of("gate.observe_wm(wm_result)")).to_equal(source.last_index_of("gate.observe_wm(wm_result)"))
expect(source.index_of("wm_producer.pump_one_published_action(shell)")).to_equal(source.last_index_of("wm_producer.pump_one_published_action(shell)"))
expect(source.index_of("wm_producer.pump_one_published_action(shell)")).to_be_less_than(source.index_of("if not wm_gate_complete:"))
expect(source).to_contain("val frame_changed = (")
expect(source).to_contain("val presented_revision = executor.render(")
expect(source).to_contain("presented_revision != snapshot.owned_scene.scene_revision")
expect(source).to_contain("if next_scanout_generation <= wm_last_scanout_generation:")
expect(source.contains("riscv64_display_boot_memory_initialize")).to_be(false)
expect(source.contains("compositor_materialize_process_surface_scalar")).to_be(false)
val module_init = "__simple_call_module_inits()"
expect(source.index_of(module_init)).to_be_greater_than(0)
expect(source.index_of(module_init)).to_equal(source.last_index_of(module_init))
```

</details>

#### admits WM readiness only after SSH recovery and scanout presentation

- admits WM readiness only after SSH recovery and scanout presentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits WM readiness only after SSH recovery and scanout presentation")
val source = file_read("examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl")
val ssh_progress = source.index_of("if gate.ssh_progress_observed and snapshot_ready:")
val engine_present = source.index_of("val wm_result = wm_producer.present_snapshot(executor, snapshot)")
val scanout_present = source.index_of("if not riscv64_display_present():")
val scanout_generation_read = source.index_of("val scanout_generation = riscv64_display_generation()")
val scanout_generation = source.index_of("if scanout_generation <= 0:")
val gate_wm = source.last_index_of("gate.observe_wm(wm_result)")
val final_verdict = source.index_of("val terminal_verdict = gate.verdict()")
val gate_complete = source.index_of("wm_gate_complete = true")
expect(ssh_progress).to_be_greater_than(0)
expect(engine_present).to_be_greater_than(ssh_progress)
expect(scanout_present).to_be_greater_than(engine_present)
expect(scanout_generation_read).to_be_greater_than(scanout_present)
expect(scanout_generation).to_be_greater_than(scanout_generation_read)
expect(gate_wm).to_be_greater_than(scanout_generation)
expect(final_verdict).to_be_greater_than(gate_wm)
expect(gate_complete).to_be_greater_than(final_verdict)
```

</details>

#### keeps one-action WM continuity interleaved with SSH recovery after readiness

- keeps one-action WM continuity interleaved with SSH recovery after readiness


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps one-action WM continuity interleaved with SSH recovery after readiness")
val source = file_read("examples/09_embedded/simple_os/arch/riscv64/ssh_live_entry.spl")
val accept_once = source.index_of("val progress = daemon.accept_and_handle_once_result()")
val pump_once = source.index_of("val _pumped = wm_producer.pump_one_published_action(shell)")
val snapshot_once = source.index_of("val snapshot = wm_producer.snapshot_published_scene(shell)")
val continuity = source.index_of("val producer_live = rv64_wm_process_liveness(wm_producer.process_id)")
val changed = source.index_of("if frame_changed:")
val render_changed = source.index_of("val presented_revision = executor.render(")
expect(accept_once).to_be_greater_than(0)
expect(pump_once).to_be_greater_than(accept_once)
expect(snapshot_once).to_be_greater_than(pump_once)
expect(continuity).to_be_greater_than(snapshot_once)
expect(changed).to_be_greater_than(continuity)
expect(render_changed).to_be_greater_than(changed)
expect(source).to_contain("not producer_live.alive")
expect(source).to_contain("if not snapshot_ready:")
expect(source).to_contain("RV64 WM continuity frame presentation failed")
expect(source).to_contain("RV64 WM continuity scanout present failed")
expect(source).to_contain("RV64 WM continuity scanout generation stalled")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/rv64_wm_boot_resources_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV64 WM boot resource admission.
- RV64 WM boot resource admission

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `309075674dc0aa7a277797a59d5cbac06950820d3a60f86798b3ca8a7f48cdf9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `309075674dc0aa7a277797a59d5cbac06950820d3a60f86798b3ca8a7f48cdf9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `309075674dc0aa7a277797a59d5cbac06950820d3a60f86798b3ca8a7f48cdf9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/rv64_wm_boot_resources_spec.spl
mirror: doc/06_spec/01_unit/os/rv64_wm_boot_resources_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=40
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/rv64_wm_boot_resources_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/rv64_wm_boot_resources_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/rv64_wm_boot_resources_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/rv64_wm_boot_resources_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/rv64_wm_boot_resources_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts only canonical 32-bit packed scanout metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/rv64_wm_boot_resources_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires one correlated process-owned content frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/rv64_wm_boot_resources_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'freezes the source-proven path and bounded pump budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
