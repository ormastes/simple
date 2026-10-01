# RISC-V Gen2 iterative M/Zmmul owner

> Exercises the closed RV32/RV64 iterative M/Zmmul product composition. The scenario proves compiler-owned provider selection, a single held-completion and retirement-owner path, deterministic strict VHDL identity, and fail-closed extension admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V Gen2 iterative M/Zmmul owner

Exercises the closed RV32/RV64 iterative M/Zmmul product composition. The scenario proves compiler-owned provider selection, a single held-completion and retirement-owner path, deterministic strict VHDL identity, and fail-closed extension admission.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/riscv_gen2_hwir_foundation.md |
| Plan | doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md |
| Design | doc/05_design/riscv_gen2_hwir_foundation.md |
| Research | doc/01_research/local/riscv_gen2_hwir_foundation.md |
| Source | `test/03_system/app/hardware/feature/riscv_gen2_muldiv_owner_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises the closed RV32/RV64 iterative M/Zmmul product composition. The
scenario proves compiler-owned provider selection, a single held-completion
and retirement-owner path, deterministic strict VHDL identity, and fail-closed
extension admission.

## Audience

Use this manual when changing scalar M/Zmmul product selection, provider
composition, completion ownership, or emitted VHDL provenance. It is for
compiler and hardware reviewers, not an ISA conformance or timing report.

## Preconditions

- The scalar product composition and strict VHDL compiler are available from
  the source under test.
- This is source-level development evidence. Generated-VHDL cycle qualification
  remains the admitted self-hosted GHDL integration scenario.

## Workflow

1. Build representative RV32 MUL and RV64 DIV products.
2. Check their iterative provider and sole retirement owner contract.
3. Render the same concrete MUL product twice and compare its identity.
4. Reject Zmmul division and base-I multiplication before a product exists.

## Examples

- RV32 `MUL x3,x1,x2` selects the iterative provider and evaluates `6 * 7` as
  `42` through its host oracle.
- RV64 `DIV x3,x1,x2` uses the same completion ownership contract and evaluates
  `100 / 7` as `14`.
- RV64 Zmmul rejects DIV, and RV64 base-I rejects MUL, before strict VHDL
  emission.

## Evidence

The first scenario checks only closed composition data: both selected products
must name `muldiv`, retain exactly one retirement owner, avoid a second
completion skid, and pass binding diagnostics. The host arithmetic values are
adjacent sanity witnesses; they are not cycle timing evidence.

The second scenario renders the same concrete RV32 MUL product twice. Equal
graph digests and byte-identical VHDL establish deterministic construction for
that fixed configuration. The emitted text must carry canonical instruction
state, completion readiness wiring, and the fault aggregator, while omitting
runtime provider and XLEN selectors.

The final scenario is fail-closed configuration evidence. It does not select a
fallback provider for an unsupported extension/opcode pairing.

## Failure handling

If a binding diagnostic becomes non-empty, inspect the product composition
before changing the test vector. If deterministic renders differ, inspect the
typed graph identity and provider selection rather than normalizing VHDL text.
If a rejected pairing compiles, stop promotion and repair admission; no emitted
artifact may be treated as a valid substitute.

## Review checklist

Before accepting a source-level result, confirm all of the following:

- The configuration is concrete RV32IM, RV64IM, or RV64 Zmmul; it is never a
  runtime extension selector.
- Exactly one provider and exactly one retirement owner are present.
- Completion remains held until its consumer accepts it.
- The two deterministic renders retain identical graph hashes and VHDL bytes.
- Unsupported M/Zmmul combinations return a diagnostic instead of falling back
  to a base-I or generic provider.

## Capture policy

The composition and deterministic-render cases expose artifact metadata for
review. The rejected-pairing case exposes its diagnostic log. None of those
captures is retained qualification evidence: the admitted qualification runner
owns immutable input binding, compiler identity, generated VHDL, GHDL logs,
and final receipt publication.

## Compatibility

This scenario covers the compiler-owned RV32IM/RV64IM and RV64 Zmmul boundary
only. It is not evidence for a generic scalar core, multiplication timing,
divide-by-zero behavior, architectural traps, out-of-order completion, or
physical implementation.

## Evidence boundary

The scenario does not prove iteration-cycle timing, GHDL execution, or a
retained qualification receipt. Those remain required external evidence.

**Requirements:** doc/02_requirements/feature/riscv_gen2_hwir_foundation.md

**Plan:** doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md

**Design:** doc/05_design/riscv_gen2_hwir_foundation.md

**Research:** doc/01_research/local/riscv_gen2_hwir_foundation.md

## Scenarios

### RISC-V Gen2 mission-critical iterative M/Zmmul product

#### should monomorphize multiply and divide into one held completion path

- Build concrete RV32 MUL and RV64 DIV scalar products
   - Artifact capture: after_step
   - Evidence: artifact verified by 10 expected checks
   - Expected: mul.provider_kind equals `muldiv`
   - Expected: div.provider_kind equals `muldiv`
   - Expected: mul.muldiv_provider != nil is true
   - Expected: div.muldiv_provider != nil is true
   - Expected: mul.retirement_owner_count equals `1`
   - Expected: div.retirement_owner_count equals `1`
   - Expected: mul.completion_skid == nil is true
   - Expected: div.completion_skid == nil is true
   - Expected: mul.binding_diagnostic() equals ``
   - Expected: div.binding_diagnostic() equals ``
- Check independent arithmetic oracle boundaries
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: evaluate_riscv_scalar_muldiv(mul_plan, 6, 7).unwrap().rd_value equals `42`
   - Expected: evaluate_riscv_scalar_muldiv(div_plan, 100, 7).unwrap().rd_value equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build concrete RV32 MUL and RV64 DIV scalar products")
val rv32 = critical_m_config(32, "rv32im")
val rv64 = critical_m_config(64, "rv64im")
val mul = strict_riscv_scalar_product_composition("g2_mul32", rv32,
    0x022081B3, LsuConfig.rv32_product_default()).unwrap()
val div = strict_riscv_scalar_product_composition("g2_div64", rv64,
    0x0220C1B3, LsuConfig.rv64_product_default()).unwrap()
expect(mul.provider_kind).to_equal("muldiv")
expect(div.provider_kind).to_equal("muldiv")
expect(mul.muldiv_provider != nil).to_equal(true)
expect(div.muldiv_provider != nil).to_equal(true)
expect(mul.retirement_owner_count).to_equal(1)
expect(div.retirement_owner_count).to_equal(1)
expect(mul.completion_skid == nil).to_equal(true)
expect(div.completion_skid == nil).to_equal(true)
expect(mul.binding_diagnostic()).to_equal("")
expect(div.binding_diagnostic()).to_equal("")

step("Check independent arithmetic oracle boundaries")
val mul_plan = strict_riscv_scalar_muldiv_projection(rv32, "iterative", 0x022081B3).unwrap()
val div_plan = strict_riscv_scalar_muldiv_projection(rv64, "iterative", 0x0220C1B3).unwrap()
expect(evaluate_riscv_scalar_muldiv(mul_plan, 6, 7).unwrap().rd_value).to_equal(42)
expect(evaluate_riscv_scalar_muldiv(div_plan, 100, 7).unwrap().rd_value).to_equal(14)
```

</details>

#### should emit deterministic strict VHDL with full identity and no runtime provider mux

- Emit the RV32 iterative multiplier product twice
   - Artifact capture: after_step
   - Evidence: artifact verified by 7 expected checks
   - Expected: first.is_success() is true
   - Expected: second.is_success() is true
   - Expected: first.route equals `hwir-gen2-scalar-product-v2`
   - Expected: first.hwir_graph_sha256 equals `second.hwir_graph_sha256`
   - Expected: first.vhdl equals `second.vhdl`
   - Expected: first.vhdl does not contain `runtime_provider`
   - Expected: first.vhdl does not contain `xlen_select`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Emit the RV32 iterative multiplier product twice")
val config = critical_m_config(32, "rv32im")
val first = compile_strict_riscv_scalar_product("g2_mul_receipt", config,
    0x022081B3, LsuConfig.rv32_product_default())
val second = compile_strict_riscv_scalar_product("g2_mul_receipt", config,
    0x022081B3, LsuConfig.rv32_product_default())
expect(first.is_success()).to_equal(true)
expect(second.is_success()).to_equal(true)
expect(first.route).to_equal("hwir-gen2-scalar-product-v2")
expect(first.hwir_graph_sha256).to_equal(second.hwir_graph_sha256)
expect(first.vhdl).to_equal(second.vhdl)
expect(first.vhdl).to_contain("canonical_instruction_reg")
expect(first.vhdl).to_contain("completion_ready=>wire_provider_completion_ready")
expect(first.vhdl).to_contain("fault_aggregator: entity work")
expect(first.vhdl.contains("runtime_provider")).to_equal(false)
expect(first.vhdl.contains("xlen_select")).to_equal(false)
```

</details>

#### should keep Zmmul fail-closed against divide and base-I against M

- Reject unsupported provider/extension combinations at elaboration
   - Log capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject unsupported provider/extension combinations at elaboration")
val zmmul = critical_m_config(64, "rv64i_zmmul")
val base = critical_m_config(64, "rv64i")
expect(strict_riscv_scalar_product_composition("bad_zmmul_div", zmmul,
    0x0220C1B3, LsuConfig.rv64_product_default()).is_err()).to_equal(true)
expect(strict_riscv_scalar_product_composition("bad_base_mul", base,
    0x022081B3, LsuConfig.rv64_product_default()).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/riscv_gen2_hwir_foundation.md`
- **Plan:** `doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md`
- **Design:** `doc/05_design/riscv_gen2_hwir_foundation.md`
- **Research:** `doc/01_research/local/riscv_gen2_hwir_foundation.md`


</details>
