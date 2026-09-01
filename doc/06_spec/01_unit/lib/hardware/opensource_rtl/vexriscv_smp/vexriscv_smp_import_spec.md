# VexRiscv-SMP Import Specification

> Verifies AC-1: at least one proven RV64 core (VexRiscv-SMP) is imported under src/lib/hardware/opensource_rtl/ with LICENSE and build docs. Tests that the import manifest, port-map API, and .v filename resolution functions return correct values.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VexRiscv-SMP Import Specification

Verifies AC-1: at least one proven RV64 core (VexRiscv-SMP) is imported under src/lib/hardware/opensource_rtl/ with LICENSE and build docs. Tests that the import manifest, port-map API, and .v filename resolution functions return correct values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-1 |
| Source | `test/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-1: at least one proven RV64 core (VexRiscv-SMP) is imported
under src/lib/hardware/opensource_rtl/ with LICENSE and build docs.
Tests that the import manifest, port-map API, and .v filename resolution
functions return correct values.

Covers:
- AC-1 (RV64 core imported with license + build docs)

## Scenarios

### VexRiscvSmpPortMap

#### AC-1: single-core port map has axi_data_width 128

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-1: single-core port map has axi_data_width 128
   - Expected: cfg.axi_data_width equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: single-core port map has axi_data_width 128")
val cfg = make_single_core_config()
expect(cfg.axi_data_width).to_equal(128)
```

</details>

#### AC-1: single-core port map has hart_count 1

- AC-1: single-core port map has hart_count 1
   - Expected: cfg.hart_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: single-core port map has hart_count 1")
val cfg = make_single_core_config()
expect(cfg.hart_count).to_equal(1)
```

</details>

#### AC-1: dual-core port map has hart_count 2

- AC-1: dual-core port map has hart_count 2
   - Expected: cfg.hart_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: dual-core port map has hart_count 2")
val cfg = make_dual_core_config()
expect(cfg.hart_count).to_equal(2)
```

</details>

#### AC-1: axi_addr_width is 32

- AC-1: axi_addr_width is 32
   - Expected: cfg.axi_addr_width equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: axi_addr_width is 32")
val cfg = make_single_core_config()
expect(cfg.axi_addr_width).to_equal(32)
```

</details>

#### AC-1: icache_size_kb is 8

- AC-1: icache_size_kb is 8
   - Expected: cfg.icache_size_kb equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: icache_size_kb is 8")
val cfg = make_single_core_config()
expect(cfg.icache_size_kb).to_equal(8)
```

</details>

### vexriscv_smp_v_filename

#### AC-1: single-core filename starts with VexRiscvLitexSmpCluster

- AC-1: single-core filename starts with VexRiscvLitexSmpCluster


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: single-core filename starts with VexRiscvLitexSmpCluster")
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_start_with("VexRiscvLitexSmpCluster")
```

</details>

#### AC-1: single-core filename contains Cc1 (1 core)

- AC-1: single-core filename contains Cc1 (1 core)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: single-core filename contains Cc1 (1 core)")
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Cc1")
```

</details>

#### AC-1: dual-core filename contains Cc2 (2 cores)

- AC-1: dual-core filename contains Cc2 (2 cores)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: dual-core filename contains Cc2 (2 cores)")
val cfg = make_dual_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Cc2")
```

</details>

#### AC-1: filename contains Iw64 (64-bit instruction bus)

- AC-1: filename contains Iw64 (64-bit instruction bus)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: filename contains Iw64 (64-bit instruction bus)")
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Iw64")
```

</details>

#### AC-1: filename contains Dw64 (64-bit data bus)

- AC-1: filename contains Dw64 (64-bit data bus)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: filename contains Dw64 (64-bit data bus)")
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Dw64")
```

</details>

#### AC-1: filename contains Ldw128 (128-bit LiteDRAM interface)

- AC-1: filename contains Ldw128 (128-bit LiteDRAM interface)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: filename contains Ldw128 (128-bit LiteDRAM interface)")
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Ldw128")
```

</details>

#### AC-1: filename ends with .v

- AC-1: filename ends with .v


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: filename ends with .v")
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_end_with(".v")
```

</details>

### vexriscv_smp_import_path

#### AC-1: import path is non-empty

- AC-1: import path is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: import path is non-empty")
val p = vexriscv_smp_import_path()
val len = p.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-1: import path contains opensource_rtl

- AC-1: import path contains opensource_rtl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: import path contains opensource_rtl")
val p = vexriscv_smp_import_path()
expect(p).to_contain("opensource_rtl")
```

</details>

#### AC-1: import path contains vexriscv_smp

- AC-1: import path contains vexriscv_smp


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-1: import path contains vexriscv_smp")
val p = vexriscv_smp_import_path()
expect(p).to_contain("vexriscv_smp")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-1`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-1`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fe078bb5650a154f02cabe27aafd19201154ba5e153718e516ac32316719a93c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fe078bb5650a154f02cabe27aafd19201154ba5e153718e516ac32316719a93c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fe078bb5650a154f02cabe27aafd19201154ba5e153718e516ac32316719a93c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: single-core port map has axi_data_width 128' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: single-core port map has hart_count 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: dual-core port map has hart_count 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
