# SStack State: vhdl-testbench-conversion

## User Request
> next task from the plan — vhdl_testbench_conversion (testbench IR, DUT extraction, stimulus/assertions, clock/reset, rendering, GHDL runner)

## Task Type
feature

## Refined Goal
> Implement VHDL testbench conversion models: testbench candidate extraction with DUT port mapping, stimulus steps and assertion models, clock/reset configuration with cycle-based timing, rendering config for combinational/clocked benches, and source-map/diagnostic hooks.

## Acceptance Criteria
- [ ] AC-1: TestbenchCandidate — test name, DUT symbol, port count, supported flag, rejection diagnostic
- [ ] AC-2: DutPort — port name, direction (in/out), bit width, sanitized VHDL name
- [ ] AC-3: StimulusStep — step index, port target, value, wait cycles
- [ ] AC-4: TestAssertion — assertion index, expected value, actual port, source line ref
- [ ] AC-5: ClockConfig — period_ns, edge (rising/falling), domain name, is_default
- [ ] AC-6: ResetSequence — reset type (sync/async), polarity (active_high/active_low), duration cycles
- [ ] AC-7: CombinationalBench — DUT ref, stimulus list, assertion list, no-clock flag
- [ ] AC-8: ClockedBench — DUT ref, clock config, reset sequence, cycle-based stimuli
- [ ] AC-9: GhdlResult — phase (analyze/elaborate/run), passed, stderr capture, exit code
- [ ] AC-10: Verification spec — 20 tests covering candidates, ports, stimuli, assertions, clock, rendering, GHDL

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across 7 plan subtasks. Existing: vhdl_testbench_converter.spl (622 lines).

### 5-implement
5 parallel Sonnet agents. 4 source + 1 test:
- src/compiler/70.backend/backend/vhdl/vhdl_testbench_model.spl — TestbenchCandidate + DutPort + StimulusStep + TestAssertion
- src/compiler/70.backend/backend/vhdl/vhdl_testbench_clock.spl — ClockConfig + ResetSequence + CycleAdvance + TimingConstraint
- src/compiler/70.backend/backend/vhdl/vhdl_testbench_render.spl — CombinationalBench + ClockedBench + GhdlResult + RenderOutput
- src/compiler/70.backend/backend/vhdl/vhdl_testbench_source.spl — SourceMapHook + TestDiagnostic + ConversionResult + PendingSpec
- test/unit/compiler/vhdl_testbench_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
