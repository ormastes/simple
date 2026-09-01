# hwir_zca_product_frontend_spec

> Exercise direct compiler API construction of bounded target-trap products.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_zca_product_frontend_spec

Exercise direct compiler API construction of bounded target-trap products.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercise direct compiler API construction of bounded target-trap products.

These checks inspect typed-HWIR product closure and serialized VHDL text. They
do not run emitted RTL, establish target equivalence, or qualify a processor or
architectural retirement producer.

## Scenarios

### RISC-V Gen2 target trap product closure

#### should preserve RV32 at 26 rows and close RV64 at exactly 32 rows

- should preserve RV32 at 26 rows and close RV64 at exactly 32 rows
- Query the direct typed-HWIR API for each concrete target row list
   - Expected: rv32.len() equals `26`
   - Expected: rv64.len() equals `32`
   - Expected: rv32 does not contain `zca.c.ld`
   - Expected: rv64 contains `zca.c.ld`
   - Expected: rv64 contains `zca.c.sd`
   - Expected: rv64 contains `zca.c.ldsp`
   - Expected: rv64 contains `zca.c.sdsp`
   - Expected: rv64 contains `zca.c.addw`
   - Expected: rv64 contains `zca.c.subw`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should preserve RV32 at 26 rows and close RV64 at exactly 32 rows")
step("Query the direct typed-HWIR API for each concrete target row list")
val rv32 = strict_zca_target_trap_migrating_isa_ids(CoreConfig.rv32_zca_cjal_mission_critical()).unwrap()
val rv64 = strict_zca_target_trap_migrating_isa_ids(CoreConfig.rv64_zca_addiw_mission_critical()).unwrap()
expect(rv32.len()).to_equal(26)
expect(rv64.len()).to_equal(32)
expect(rv32.contains("zca.c.ld")).to_equal(false)
expect(rv64.contains("zca.c.ld")).to_equal(true)
expect(rv64.contains("zca.c.sd")).to_equal(true)
expect(rv64.contains("zca.c.ldsp")).to_equal(true)
expect(rv64.contains("zca.c.sdsp")).to_equal(true)
expect(rv64.contains("zca.c.addw")).to_equal(true)
expect(rv64.contains("zca.c.subw")).to_equal(true)
```

</details>

#### should use one row-level ambiguity guard for all RV64 rows

- should use one row-level ambiguity guard for all RV64 rows
- Build the bounded RV64 typed-HWIR product and inspect origin ownership
   - Expected: module.shape_diagnostic() equals ``
   - Expected: overlap_origins equals `1`
   - Expected: has_ld and has_sd and has_ldsp and has_sdsp and has_addw and has_subw is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should use one row-level ambiguity guard for all RV64 rows")
step("Build the bounded RV64 typed-HWIR product and inspect origin ownership")
val module = strict_zca_rv64_full_trap_migrating_predecode_hwir(
    "riscv_gen2_zca_rv64_addiw_trap_migrating_predecode",
    CoreConfig.rv64_zca_addiw_mission_critical()).unwrap()
var overlap_origins = 0
var has_ld = false
var has_sd = false
var has_ldsp = false
var has_sdsp = false
var has_addw = false
var has_subw = false
for origin in module.origins:
    if origin.source_name.ends_with(".overlap_guard"): overlap_origins = overlap_origins + 1
    if origin.source_name.contains("c.ld"): has_ld = true
    if origin.source_name.contains("c.sd"): has_sd = true
    if origin.source_name.contains("c.ldsp"): has_ldsp = true
    if origin.source_name.contains("c.sdsp"): has_sdsp = true
    if origin.source_name.contains("c.addw"): has_addw = true
    if origin.source_name.contains("c.subw"): has_subw = true
expect(module.shape_diagnostic()).to_equal("")
expect(overlap_origins).to_equal(1)
expect(has_ld and has_sd and has_ldsp and has_sdsp and has_addw and has_subw).to_equal(true)
```

</details>

#### should emit a deterministic typed RV64 stateful product graph

- should emit a deterministic typed RV64 stateful product graph
   - Artifact capture: after_step
- Compile the bounded RV64 stateful product twice through the direct compiler API
   - Artifact capture: after_step
   - Evidence: artifact verified by 4 expected checks
   - Expected: first.is_success() is true
   - Expected: second.is_success() is true
   - Expected: first.hwir_graph_sha256 equals `second.hwir_graph_sha256`
   - Expected: first.hwir_graph_sha256.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should emit a deterministic typed RV64 stateful product graph")
step("Compile the bounded RV64 stateful product twice through the direct compiler API")
val config = CoreConfig.rv64_zca_addiw_mission_critical()
val first = compile_strict_zca_trap_single_outstanding_frontend_product(config)
val second = compile_strict_zca_trap_single_outstanding_frontend_product(config)
expect(first.is_success()).to_equal(true)
expect(second.is_success()).to_equal(true)
expect(first.hwir_graph_sha256).to_equal(second.hwir_graph_sha256)
expect(first.hwir_graph_sha256.len()).to_equal(64)
expect(first.vhdl).to_contain("entity riscv_gen2_zca_rv64_addiw_trap_migrating_predecode is")
expect(first.vhdl).to_contain("global_overlap_after_31")
expect(first.vhdl).to_contain("cld_match_legal")
expect(first.vhdl).to_contain("sdsp64_match_legal")
expect(first.vhdl).to_contain("caddw64_match_legal")
```

</details>

#### should reject the full RV64 graph for every RV32 product

- should reject the full RV64 graph for every RV32 product
- Attempt the bounded RV64 graph under the incompatible RV32 product profile
   - Expected: rejected.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("should reject the full RV64 graph for every RV32 product")
step("Attempt the bounded RV64 graph under the incompatible RV32 product profile")
val rejected = strict_zca_rv64_full_trap_migrating_predecode_hwir(
    "rv32_must_fail", CoreConfig.rv32_zca_cjal_mission_critical())
expect(rejected.is_err()).to_equal(true)
expect(rejected.err().unwrap()).to_start_with("HWIR-E-ZCA-RV64-FULL-PROFILE")
```

</details>

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7bf11ccd9ab7671dc7550ac8050a1c95efd5c0866f888373cadcc6d8237b205c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7bf11ccd9ab7671dc7550ac8050a1c95efd5c0866f888373cadcc6d8237b205c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7bf11ccd9ab7671dc7550ac8050a1c95efd5c0866f888373cadcc6d8237b205c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve RV32 at 26 rows and close RV64 at exactly 32 rows' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve RV32 at 26 rows and close RV64 at exactly 32 rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use one row-level ambiguity guard for all RV64 rows' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should use one row-level ambiguity guard for all RV64 rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit a deterministic typed RV64 stateful product graph' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should emit a deterministic typed RV64 stateful product graph' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_zca_product_frontend_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject the full RV64 graph for every RV32 product' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
