# VHDL-PARITY-012: Testbench Conversion

Owner: Worker E
Status: Pending
Scope: First runnable converter for one-DUT Simple hardware tests. This task
plan is implementation-ready, but this file only assigns work; implementation
workers must keep edits inside their assigned files.

## Goal

Convert Simple hardware tests into executable VHDL testbenches so generated
RTL can be validated by GHDL and, later, by vendor simulators with the same
stimulus and expected behavior used by Simple specs.

## Source Model

The first supported source should be a Simple spec or test function that names
one `@hardware` function as the device under test. The conversion must reject
tests that depend on unsupported host-only behavior instead of silently
dropping assertions.

Supported test content:

- literal scalar stimuli for bool, integer, enum, and fixed-width bit values
  once those hardware types are supported
- labeled tuple inputs and outputs after bundle flattening is available
- sequential stimulus steps with explicit waits or clock-cycle advances
- `expect(actual).to_equal(expected)` assertions over DUT outputs
- setup reset sequences for clocked hardware

Unsupported test content should produce a diagnostic that names the unsupported
construct and the source test.

## First Runnable Converter Slice

The initial implementation is intentionally narrow. It should convert one
Simple test into one VHDL testbench when the test has a single DUT, literal
stimuli, and `expect(...).to_equal(...)` assertions. All other constructs must
fail before VHDL emission with a diagnostic that includes the test name and the
unsupported construct.

Supported in slice 1:

- combinational `@hardware` DUTs with scalar inputs and scalar or labeled tuple
  outputs
- clocked `@hardware` DUTs that already have reset-domain metadata from
  `@clocked` or the reset-domain implementation slice
- literal bool, integer, and fixed-width bit-vector stimuli when the DUT port
  type is already supported by VHDL lowering
- direct output reads, including labeled tuple outputs after flattening
- `expect(actual).to_equal(expected)` only
- deterministic GHDL analyze, elaborate, and run command reporting

Rejected in slice 1:

- more than one DUT per test
- loops, branches, randomization, host file I/O, heap values, dynamic
  allocation, indirect calls, and arbitrary helper calls inside the converted
  test body
- unsupported matchers such as `to_contain`, `to_be_greater_than`, and custom
  matcher functions
- multi-clock or cross-domain tests
- payload enums, dynamic arrays, unconstrained vectors, and composite values
  that do not have a defined VHDL port flattening rule

## File Ownership For Implementation

Workers must not edit outside their assigned ownership without reassigning the
task in this document first.

- Worker E1 owns public driver/test command plumbing:
  `src/compiler_rust/driver/src/cli/**`,
  `src/compiler_rust/driver/src/commands/**`, and public command docs.
- Worker E2 owns converter extraction and intermediate model:
  `src/compiler_rust/compiler/src/pipeline/vhdl_testbench.rs` and any module
  declaration needed to expose it from the compiler crate.
- Worker E3 owns VHDL testbench rendering:
  `src/compiler_rust/compiler/src/pipeline/vhdl_testbench_render.rs`.
- Worker E4 owns simulator runner integration:
  `src/compiler_rust/compiler/src/pipeline/vhdl_sim_runner.rs` or the existing
  closest runner module if one already exists.
- Worker E5 owns runnable specs:
  `test/system/compiler/vhdl_testbench_conversion_spec.spl`,
  `test/system/compiler/vhdl_clocked_testbench_conversion_spec.spl`, and
  `test/system/compiler/vhdl_sim_runner_integration_spec.spl`.
- Worker E6 owns docs and pending backlog maintenance:
  this file and `test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip`.

## API Surface

Expose a small compiler API so the driver and specs do not depend on renderer
internals.

```rust
pub struct VhdlTestbenchOptions {
    pub std: VhdlStandard,
    pub clock_period_ns: u64,
    pub finish_with_std_env: bool,
    pub keep_work_files: bool,
}

pub struct VhdlTestbenchArtifact {
    pub dut_entity: String,
    pub testbench_entity: String,
    pub dut_vhdl: String,
    pub testbench_vhdl: String,
    pub source_map_json: Option<String>,
}

pub struct VhdlSimulationResult {
    pub analyzed: bool,
    pub elaborated: bool,
    pub simulated: bool,
    pub stdout: String,
    pub stderr: String,
}

pub fn generate_vhdl_testbench(
    source: &str,
    test_name: &str,
    options: &VhdlTestbenchOptions,
) -> Result<VhdlTestbenchArtifact, Diagnostic>;

pub fn run_vhdl_testbench_with_ghdl(
    artifact: &VhdlTestbenchArtifact,
    options: &VhdlTestbenchOptions,
) -> Result<VhdlSimulationResult, Diagnostic>;
```

The API may use existing repo diagnostic/result types instead of the exact
names above, but it must preserve the same information. The renderer must be
pure and deterministic; filesystem writes and process execution belong only in
the runner or driver layer.

## Implementation Subtasks

1. Extract testbench candidates from Simple specs.
   - Input: source text plus selected test name.
   - Output: one DUT symbol, ordered stimulus steps, expected assertions, and
     optional clock/reset metadata.
   - Acceptance: unsupported tests fail with a diagnostic before any VHDL text
     is emitted.

2. Build a testbench IR.
   - Model DUT ports using the same sanitized/flattened port names as RTL
     generation.
   - Preserve source expectation indexes for assertion messages.
   - Acceptance: repeated conversion of the same source produces stable IR
     ordering.

3. Render combinational testbenches.
   - Emit no-port entity, DUT instance, signals, stimulus process,
     assertions, and deterministic finish.
   - Acceptance: GHDL analysis, elaboration, and simulation pass for at least
     one scalar DUT and one labeled-output DUT.

4. Render clocked testbenches.
   - Emit clock generator, reset sequence, cycle-based stimuli, and assertions
     after expected latency.
   - Acceptance: GHDL simulation observes reset behavior and fails if expected
     latency is wrong.

5. Integrate GHDL runner results.
   - Surface analyze, elaborate, and run failures as failing Simple test
     results with command phase and stderr context.
   - Acceptance: deliberately invalid generated VHDL and deliberately failing
     assertions both fail the Simple test.

6. Add source-map hooks.
   - Include test name, expectation index, generated entity, DUT instance, and
     port/signal origins when source-map support exists.
   - Acceptance: source-map fields are deterministic and absent only when the
     caller explicitly disables sidecar output.

7. Demote completed pending specs.
   - Move runnable cases from the skip backlog into system specs as each
     subtask lands.
   - Acceptance: pending list only contains unimplemented behavior.

## Generated VHDL Shape

Each converted test emits a standalone testbench entity with no ports and an
architecture containing:

- DUT component or direct entity instantiation
- one signal per DUT input and output port, using the same sanitized names as
  generated RTL
- optional clock generator process with a deterministic `CLK_PERIOD`
- optional reset process matching the DUT reset-domain polarity and synchrony
- stimulus process that applies inputs in source order
- assertion statements that report the originating Simple expectation
- final pass marker and `std.env.finish` when available

The testbench must be deterministic: two conversions of the same source should
produce byte-stable VHDL except for explicitly documented source-map comments.

## Clock And Reset Behavior

Clocked DUT tests must describe time in clock cycles, not backend-specific
wall-clock sleeps.

Required behavior:

- default clock period is 10 ns unless the test or hardware domain overrides it
- active-low and active-high resets use the reset-domain metadata
- asynchronous reset is asserted before the first rising edge and released
  before stimulus begins
- synchronous reset is sampled on a rising edge before stimulus begins
- no-reset domains omit reset generation and start from explicit initial
  stimulus
- multi-domain DUTs are rejected until multi-clock testbench semantics are
  specified

## Assertions And Pass/Fail

Simple expectations lower to VHDL `assert` statements. Failed assertions must
make the simulator return failure through severity `failure` or the selected
runner's equivalent.

Required assertion mapping:

- `expect(x).to_equal(y)` emits an equality assertion
- assertion messages include the Simple test name and expectation index
- bool and bit-vector values render with readable expected/actual context where
  the VHDL type supports image conversion
- unsupported matchers are rejected with a diagnostic

The runner considers the converted test passed only when analysis, elaboration,
and simulation all succeed.

## Acceptance Criteria

- A combinational `@hardware` function test converts to a VHDL testbench with
  stimuli, assertions, and a deterministic finish path.
- A clocked DUT test converts to a testbench with clock generation, reset
  sequencing, cycle-based stimuli, and output assertions after the expected
  latency.
- Labeled tuple output assertions use flattened/sanitized output signal names.
- Unsupported Simple spec features are rejected before VHDL emission with
  source-test diagnostics.
- GHDL analysis, elaboration, and simulation failure are surfaced as failing
  Simple test results.
- Passing converted tests report success only after the simulator completes.
- Converter output is byte-stable for the same source, options, and Simple
  compiler version.
- Unsupported constructs are rejected before any partial artifact is returned.

## Pending SPipe Coverage

Pending coverage lives in
`test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip` until implementation
creates runnable system specs. Runnable specs should later move to:

- `test/system/compiler/vhdl_testbench_conversion_spec.spl`
- `test/system/compiler/vhdl_clocked_testbench_conversion_spec.spl`
- `test/system/compiler/vhdl_sim_runner_integration_spec.spl`

## Verification Commands

```sh
bin/simple test --only-skipped --list-skip-features --pending test/unit/compiler/vhdl_python_hdl_parity_spec.spl.skip
bin/simple test test/system/compiler/vhdl_testbench_conversion_spec.spl
ghdl -a --std=08 <generated_dut>.vhdl <generated_tb>.vhdl
ghdl -e --std=08 <testbench_entity>
ghdl -r --std=08 <testbench_entity>
```
