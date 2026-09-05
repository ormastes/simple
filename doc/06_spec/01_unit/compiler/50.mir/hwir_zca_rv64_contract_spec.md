# hwir_zca_rv64_contract_spec

> Exercise only the closed source-level identity set for isolated RV64 Zca rows.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_zca_rv64_contract_spec

Exercise only the closed source-level identity set for isolated RV64 Zca rows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_zca_rv64_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercise only the closed source-level identity set for isolated RV64 Zca rows.

This companion checks reserved MIR names and the bounded evidence allowlist. It
does not execute generated RTL, establish complete Zca behavior, or qualify a
hardware product.

## Scenarios

### closed RV64 Zca row contract

#### should pin exact intrinsic and ISA identities without product qualification

- should pin exact intrinsic and ISA identities without product qualification
- Read the closed RV64 row identity and evidence lists
   - Expected: intrinsics.len() equals `9`
   - Expected: isa_ids.len() equals `9`
   - Expected: intrinsics[0] equals `__simple_riscv_zca_cld_rv64_row_v1`
   - Expected: intrinsics[8] equals `__simple_riscv_zca_srai6_rv64_row_v1`
   - Expected: isa_ids[0] equals `zca.rv64.c.ld`
   - Expected: isa_ids[8] equals `zca.rv64.c.srai6`
   - Expected: strict_zca_rv64_row_evidence_allowlist() equals `isa_ids`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should pin exact intrinsic and ISA identities without product qualification")
step("Read the closed RV64 row identity and evidence lists")
val intrinsics = strict_zca_rv64_row_intrinsic_ids()
val isa_ids = strict_zca_rv64_row_isa_ids()
expect(intrinsics.len()).to_equal(9)
expect(isa_ids.len()).to_equal(9)
expect(intrinsics[0]).to_equal("__simple_riscv_zca_cld_rv64_row_v1")
expect(intrinsics[8]).to_equal("__simple_riscv_zca_srai6_rv64_row_v1")
expect(isa_ids[0]).to_equal("zca.rv64.c.ld")
expect(isa_ids[8]).to_equal("zca.rv64.c.srai6")
expect(strict_zca_rv64_row_evidence_allowlist()).to_equal(isa_ids)
```

</details>

#### should admit exact local identifiers and reject prefix lookalikes

- should admit exact local identifiers and reject prefix lookalikes
- Probe the local intrinsic admission boundary with exact and lookalike names
   - Expected: is_strict_zca_rv64_row_intrinsic("__simple_riscv_zca_caddw_rv64_row_v1") is true
   - Expected: is_strict_zca_rv64_row_intrinsic("__simple_riscv_zca_caddw_rv64_row_v1_extra") is false
   - Expected: is_strict_zca_rv64_row_intrinsic("__simple_riscv_zca_unknown_rv64_row_v1") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should admit exact local identifiers and reject prefix lookalikes")
step("Probe the local intrinsic admission boundary with exact and lookalike names")
expect(is_strict_zca_rv64_row_intrinsic("__simple_riscv_zca_caddw_rv64_row_v1")).to_equal(true)
expect(is_strict_zca_rv64_row_intrinsic("__simple_riscv_zca_caddw_rv64_row_v1_extra")).to_equal(false)
expect(is_strict_zca_rv64_row_intrinsic("__simple_riscv_zca_unknown_rv64_row_v1")).to_equal(false)
```

</details>

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6496546c156ee105f780acbd5184e5afb2e9898f3793a6a73f7c349f95f9b495`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6496546c156ee105f780acbd5184e5afb2e9898f3793a6a73f7c349f95f9b495`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6496546c156ee105f780acbd5184e5afb2e9898f3793a6a73f7c349f95f9b495`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/50.mir/hwir_zca_rv64_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_zca_rv64_contract_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_rv64_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_rv64_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_zca_rv64_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_zca_rv64_contract_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pin exact intrinsic and ISA identities without product qualification' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_rv64_contract_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should pin exact intrinsic and ISA identities without product qualification' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_rv64_contract_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should admit exact local identifiers and reject prefix lookalikes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_rv64_contract_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should admit exact local identifiers and reject prefix lookalikes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
