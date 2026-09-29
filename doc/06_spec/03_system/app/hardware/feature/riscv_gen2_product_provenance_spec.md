# riscv_gen2_product_provenance_spec

> Direct compiler API calls bind compiler-owned Gen2 products to concrete

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# riscv_gen2_product_provenance_spec

Direct compiler API calls bind compiler-owned Gen2 products to concrete

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Direct compiler API calls bind compiler-owned Gen2 products to concrete
configuration, decoder identity, and graph closure in emitted VHDL provenance.
These checks are pre-HDL-simulation evidence only; they do not create a
self-hosted RTL or target-qualification claim.

## Scenarios

### RISC-V Gen2 typed product provenance

#### should bind RV32 stateful VHDL to its closure graph

- should bind RV32 stateful VHDL to its closure graph
   - Artifact capture: after_step
- Render the RV32 stateful product through the direct compiler API
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: product.is_success() is true
   - Expected: product.route equals `hwir-gen2-stateful-product-v2`
   - Expected: product.hwir_graph_sha256.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind RV32 stateful VHDL to its closure graph")
step("Render the RV32 stateful product through the direct compiler API")
val product = compile_strict_zca_single_outstanding_frontend_product(CoreConfig.rv32_zca_mission_critical())
expect(product.is_success()).to_equal(true)
expect(product.route).to_equal("hwir-gen2-stateful-product-v2")
expect(product.hwir_graph_sha256.len()).to_equal(64)
expect(product.vhdl).to_contain("graph=" + product.hwir_graph_sha256)
expect(product.vhdl).to_contain("profile=riscv-gen2-rv32-zca-critical")
expect(product.vhdl).to_contain("-- simple-hwir node=riscv_gen2_zca_single_outstanding_frontend_rv32:sequential:register:valid_reg")
expect(product.vhdl).to_contain("-- simple-hwir node=riscv_gen2_zca_single_outstanding_frontend_rv32:sequential:rule:retire_match")
```

</details>

#### should bind RV64 trap-stateful VHDL to its closure graph

- should bind RV64 trap-stateful VHDL to its closure graph
   - Artifact capture: after_step
- Render the RV64 trap-stateful product through the direct compiler API
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: product.is_success() is true
   - Expected: product.route equals `hwir-gen2-trap-stateful-product-v3`
   - Expected: product.hwir_graph_sha256.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind RV64 trap-stateful VHDL to its closure graph")
step("Render the RV64 trap-stateful product through the direct compiler API")
val product = compile_strict_zca_trap_single_outstanding_frontend_product(CoreConfig.rv64_zca_mission_critical())
expect(product.is_success()).to_equal(true)
expect(product.route).to_equal("hwir-gen2-trap-stateful-product-v3")
expect(product.hwir_graph_sha256.len()).to_equal(64)
expect(product.vhdl).to_contain("graph=" + product.hwir_graph_sha256)
expect(product.vhdl).to_contain("profile=riscv-gen2-rv64-zca-critical")
expect(product.vhdl).to_contain("-- simple-hwir node=riscv_gen2_zca_trap_single_outstanding_frontend_rv64:sequential:output:trap_valid")
```

</details>

#### should bind each specialized trap v3 product to its concrete decoder only

- should bind each specialized trap v3 product to its concrete decoder only
   - Artifact capture: after_step
- Render the two closed target-specific trap products through their direct compiler APIs
   - Artifact capture: after_step
   - Evidence: artifact verified by 8 expected checks
   - Expected: rv32.is_success() is true
   - Expected: rv32.route equals `hwir-gen2-trap-stateful-product-v3`
   - Expected: rv32.hwir_graph_sha256.len() equals `64`
   - Expected: rv32.vhdl does not contain `riscv_gen2_zca_rv64_addiw_trap_migrating_predecode`
   - Expected: rv64.is_success() is true
   - Expected: rv64.route equals `hwir-gen2-trap-stateful-product-v3`
   - Expected: rv64.hwir_graph_sha256.len() equals `64`
   - Expected: rv64.vhdl does not contain `riscv_gen2_zca_rv32_cjal_trap_migrating_predecode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bind each specialized trap v3 product to its concrete decoder only")
step("Render the two closed target-specific trap products through their direct compiler APIs")
val rv32 = compile_strict_zca_trap_single_outstanding_frontend_product(CoreConfig.rv32_zca_cjal_mission_critical())
expect(rv32.is_success()).to_equal(true)
expect(rv32.route).to_equal("hwir-gen2-trap-stateful-product-v3")
expect(rv32.hwir_graph_sha256.len()).to_equal(64)
expect(rv32.vhdl).to_contain("profile=riscv-gen2-rv32-zca-cjal-critical")
expect(rv32.vhdl).to_contain("child: entity work.riscv_gen2_zca_rv32_cjal_trap_migrating_predecode")
expect(rv32.vhdl.contains("riscv_gen2_zca_rv64_addiw_trap_migrating_predecode")).to_equal(false)
val rv64 = compile_strict_zca_trap_single_outstanding_frontend_product(CoreConfig.rv64_zca_addiw_mission_critical())
expect(rv64.is_success()).to_equal(true)
expect(rv64.route).to_equal("hwir-gen2-trap-stateful-product-v3")
expect(rv64.hwir_graph_sha256.len()).to_equal(64)
expect(rv64.vhdl).to_contain("profile=riscv-gen2-rv64-zca-addiw-critical")
expect(rv64.vhdl).to_contain("child: entity work.riscv_gen2_zca_rv64_addiw_trap_migrating_predecode")
expect(rv64.vhdl.contains("riscv_gen2_zca_rv32_cjal_trap_migrating_predecode")).to_equal(false)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da5895f53b1e828f6993809b927d32c49fa347f05377015d056b01902144bf2b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da5895f53b1e828f6993809b927d32c49fa347f05377015d056b01902144bf2b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da5895f53b1e828f6993809b927d32c49fa347f05377015d056b01902144bf2b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.spl
mirror: doc/06_spec/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.spl:22:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind RV32 stateful VHDL to its closure graph' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bind RV32 stateful VHDL to its closure graph' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind RV64 trap-stateful VHDL to its closure graph' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bind RV64 trap-stateful VHDL to its closure graph' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bind each specialized trap v3 product to its concrete decoder only' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/hardware/feature/riscv_gen2_product_provenance_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should bind each specialized trap v3 product to its concrete decoder only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
