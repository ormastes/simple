# RISC-V Gen2 FENCE accepted-effect cycle evidence

> Exercises the generated RV32 FENCE owner through a clocked VHDL testbench. The witness proves an accepted FENCE effect is held until its effect consumer is ready, yields one precise completion, and suppresses effects for an illegal dispatch while preserving the expected trap.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V Gen2 FENCE accepted-effect cycle evidence

Exercises the generated RV32 FENCE owner through a clocked VHDL testbench. The witness proves an accepted FENCE effect is held until its effect consumer is ready, yields one precise completion, and suppresses effects for an illegal dispatch while preserving the expected trap.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | doc/02_requirements/feature/riscv_gen2_hwir_foundation.md |
| Plan | doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md |
| Design | doc/05_design/riscv_gen2_hwir_foundation.md |
| Research | doc/01_research/local/riscv_gen2_hwir_foundation.md |
| Source | `test/02_integration/compiler/riscv_scalar_fence_cycle_ghdl_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises the generated RV32 FENCE owner through a clocked VHDL testbench. The
witness proves an accepted FENCE effect is held until its effect consumer is
ready, yields one precise completion, and suppresses effects for an illegal
dispatch while preserving the expected trap.

## Audience

Use this scenario when changing FENCE effect ownership, completion sequencing,
illegal instruction handling, or the VHDL interface of the FENCE owner.

## Preconditions

- A VHDL-2008-capable GHDL runner is available.
- The strict RV32 FENCE owner compiler is available from the source under test.

## Workflow

1. Require GHDL; absence is a blocked test failure, never a skip.
2. Compile the fixed `FENCE` instruction through the strict FENCE owner.
3. Analyze, elaborate, and simulate the generated product plus testbench.
4. Verify held effect, exact fields, one completion, and illegal suppression.

## Examples

- The fixed `FENCE` vector carries `fm=0`, `pred=15`, and `succ=15`.
- The effect remains valid while its effect-ready input is low.
- A single accepted effect produces a single held completion.
- An illegal dispatch produces the precise illegal trap without a fence effect.

## Captured evidence

The scenario captures execution, generated-artifact, and log evidence for its
single RV32 witness. The `/tmp/fence_cycle.vhd` file is diagnostic-only. An
admitted qualification run must retain its own bound VHDL, GHDL, and manifest
artifacts rather than relying on this transient path.

## Review checklist

Before accepting a diagnostic result, confirm that:

- GHDL availability is asserted before product construction.
- The product configuration is concrete RV32 and fixed to FENCE.
- Effect validity remains asserted until effect-ready is observed.
- The emitted fields equal the fixed FM/PRED/SUCC witness.
- Completion becomes valid only after effect acceptance.
- Completion is held until its own ready handshake.
- The illegal case emits no effect and reports the expected trap cause/tval.

## Evidence boundary

This is development-stage host evidence. It is not an admitted self-hosted
qualification receipt, a full memory-ordering proof, or a complete processor
claim. The qualification runner must retain compiler, VHDL, manifest, and GHDL
receipts separately.

## Failure handling

On failure, retain the transient `/tmp/fence_cycle.vhd` diagnostic artifact and
inspect the analyzer or simulator output. Do not weaken effect-held, completion,
or illegal-trap assertions to accommodate a changed implementation.

## Compatibility and limitations

The scenario proves one accepted-effect owner interaction, not the complete
RISC-V memory model, cache behavior, I/O ordering, FENCE.I, or multiprocessor
ordering. It is compatible only with the closed strict FENCE owner. A legacy
decoder, host-only ordering model, or hand-written test fixture cannot replace
the generated product in this evidence path.

The testbench intentionally omits fetch, memory, and external retirement
composition. Future processor evidence must preserve these owner/handshake
properties while connecting the generated FENCE product to architectural state.

## Operator handoff

When this scenario passes on an admitted toolchain, retain the generated VHDL,
the exact testbench text, analyze/elaborate/run logs, compiler identity, and
product manifest in the qualification envelope. A green developer-host result
must remain diagnostic until the qualification writer validates and publishes
the bound receipt. If GHDL is unavailable, preserve the blocked result and
resume only after the host dependency is installed; never turn this row into a
skip or a source-text-only assertion.

The receipt must record target profile, configuration identity, graph digest,
and exact GHDL command outcomes. Missing any one of those fields leaves this
scenario as planned qualification evidence rather than a release result.
The required receipt writer is the sole promotion authority.
Manual inspection remains required after every generated-artifact change.

**Requirements:** doc/02_requirements/feature/riscv_gen2_hwir_foundation.md

**Plan:** doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md

**Design:** doc/05_design/riscv_gen2_hwir_foundation.md

**Research:** doc/01_research/local/riscv_gen2_hwir_foundation.md

## Scenarios

### RISC-V Gen2 fence accepted-effect cycle evidence

<details>
<summary>Advanced: should simulate held effect precise completion and illegal suppression</summary>

#### should simulate held effect precise completion and illegal suppression _(slow)_

- Require the external GHDL VHDL-2008 cycle runner
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: available is true
- Build and simulate the accepted FENCE effect witness
   - Log capture: after_step
   - Evidence: log output verified by 5 expected checks
   - Expected: emitted.is_success() is true
   - Expected: vhdl_write_file(path, emitted.vhdl + "\n" + fence_testbench()) is true
   - Expected: ghdl_analyze(path).success is true
   - Expected: ghdl_elaborate("fence_cycle_tb").success is true
   - Expected: ghdl_run("fence_cycle_tb", Some("500ns")).success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Require the external GHDL VHDL-2008 cycle runner")
val available = ghdl_available()
expect(available).to_equal(true)
if not available:
    val blocked = "BLOCKED: GHDL VHDL-2008 runner is unavailable; cannot satisfy REQ-G2-017"
    print blocked
    fail(blocked)
    return
step("Build and simulate the accepted FENCE effect witness")
val emitted = compile_strict_riscv_scalar_fence_owner(
    "fence_cycle", CoreConfig.rv32(), 0x0FF0000F)
expect(emitted.is_success()).to_equal(true)
if emitted.is_success():
    val path = "/tmp/fence_cycle.vhd"
    expect(vhdl_write_file(path, emitted.vhdl + "\n" + fence_testbench())).to_equal(true)
    expect(ghdl_analyze(path).success).to_equal(true)
    expect(ghdl_elaborate("fence_cycle_tb").success).to_equal(true)
    expect(ghdl_run("fence_cycle_tb", Some("500ns")).success).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/riscv_gen2_hwir_foundation.md`
- **Plan:** `doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md`
- **Design:** `doc/05_design/riscv_gen2_hwir_foundation.md`
- **Research:** `doc/01_research/local/riscv_gen2_hwir_foundation.md`


</details>
