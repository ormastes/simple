# Target Family Package Surface Specification

> Tests covering MIR optimizer target-family package surface.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Target Family Package Surface Specification

## Scenarios

### MIR optimizer target-family package surface

#### classifies representative hosted and embedded triples

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies representative hosted and embedded triples
   - Expected: target_family_from_triple("x86_64-unknown-linux-gnu") equals `X86_64`
   - Expected: target_family_enum_from_triple("aarch64-apple-macosx") equals `TargetFamily.Aarch64`
   - Expected: target_family_name(TargetFamily.Rv32) equals `Rv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("classifies representative hosted and embedded triples")
expect(target_family_from_triple("x86_64-unknown-linux-gnu")).to_equal("X86_64")
expect(target_family_enum_from_triple("aarch64-apple-macosx")).to_equal(TargetFamily.Aarch64)
expect(target_family_name(TargetFamily.Rv32)).to_equal("Rv32")
```

</details>

#### builds target feature metadata through the package API

- builds target feature metadata through the package API
   - Expected: features.family equals `TargetFamily.Rv64`
   - Expected: features.features.len() equals `2`
   - Expected: features.features[0] equals `v`
   - Expected: features.features[1] equals `zbb`
   - Expected: features.opt_level equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds target feature metadata through the package API")
val features = target_feature_set_new("riscv64-unknown-linux-gnu", ["v", "zbb"])
expect(features.family).to_equal(TargetFamily.Rv64)
expect(features.features.len()).to_equal(2)
expect(features.features[0]).to_equal("v")
expect(features.features[1]).to_equal("zbb")
expect(features.strict).to_be(false)
expect(features.opt_level).to_equal(2)
```

</details>

#### constructs MIR variants whose payload types are part of the package facade

- constructs MIR variants whose payload types are part of the package facade


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("constructs MIR variants whose payload types are part of the package facade")
val pointer = MirOperand.copy(LocalId(id: 1))
val value = MirOperand.copy(LocalId(id: 2))
val barrier = MirInstKind.GpuBarrier(GpuBarrierScope.Workgroup)
val atomic = MirInstKind.GpuAtomicOp(LocalId(id: 3), GpuAtomicOpKind.Add, pointer, value)
val process = MirInstKind.VhdlProcess(VhdlProcessKind.Combinational(["clock", "reset"]), BlockId(id: 7))

expect(package_gpu_barrier_is_workgroup(barrier)).to_be(true)
expect(package_gpu_atomic_is_add(atomic)).to_be(true)
expect(package_vhdl_process_is_combinational(process)).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir_opt/target_family_package_surface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MIR optimizer target-family package surface.
- MIR optimizer target-family package surface

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `456001e4ee3c34758ba22b00cf5cc2b74ae83cc3bddc65dca51ebf6f63134482`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `456001e4ee3c34758ba22b00cf5cc2b74ae83cc3bddc65dca51ebf6f63134482`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `456001e4ee3c34758ba22b00cf5cc2b74ae83cc3bddc65dca51ebf6f63134482`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/mir_opt/target_family_package_surface_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir_opt/target_family_package_surface_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir_opt/target_family_package_surface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir_opt/target_family_package_surface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir_opt/target_family_package_surface_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir_opt/target_family_package_surface_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies representative hosted and embedded triples' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/target_family_package_surface_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds target feature metadata through the package API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir_opt/target_family_package_surface_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs MIR variants whose payload types are part of the package facade' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
