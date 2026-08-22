# VexRiscv-SMP Import Specification

> Verifies the vexriscv smp import behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VexRiscv-SMP Import Specification

Verifies the vexriscv smp import behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-1 |
| Source | `test/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the vexriscv smp import behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### VexRiscvSmpPortMap

#### AC-1: single-core port map has axi_data_width 128

- Verify: AC-1: single-core port map has axi_data_width 128
   - Expected: cfg.axi_data_width equals `128)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: single-core port map has axi_data_width 128")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = make_single_core_config()
expect(cfg.axi_data_width).to_equal(128)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-1: single-core port map has hart_count 1

- Verify: AC-1: single-core port map has hart_count 1
   - Expected: cfg.hart_count equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: single-core port map has hart_count 1")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = make_single_core_config()
expect(cfg.hart_count).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-1: dual-core port map has hart_count 2

- Verify: AC-1: dual-core port map has hart_count 2
   - Expected: cfg.hart_count equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: dual-core port map has hart_count 2")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = make_dual_core_config()
expect(cfg.hart_count).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-1: axi_addr_width is 32

- Verify: AC-1: axi_addr_width is 32
   - Expected: cfg.axi_addr_width equals `32)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: axi_addr_width is 32")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = make_single_core_config()
expect(cfg.axi_addr_width).to_equal(32)  # oracle: pinned constant asserted by this scenario
```

</details>

#### AC-1: icache_size_kb is 8

- Verify: AC-1: icache_size_kb is 8
   - Expected: cfg.icache_size_kb equals `8)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: icache_size_kb is 8")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = make_single_core_config()
expect(cfg.icache_size_kb).to_equal(8)  # oracle: pinned constant asserted by this scenario
```

</details>

### vexriscv_smp_v_filename

#### AC-1: single-core filename starts with VexRiscvLitexSmpCluster

- Verify: AC-1: single-core filename starts with VexRiscvLitexSmpCluster


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: single-core filename starts with VexRiscvLitexSmpCluster")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_start_with("VexRiscvLitexSmpCluster")
```

</details>

#### AC-1: single-core filename contains Cc1 (1 core)

- Verify: AC-1: single-core filename contains Cc1 (1 core)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: single-core filename contains Cc1 (1 core)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Cc1")
```

</details>

#### AC-1: dual-core filename contains Cc2 (2 cores)

- Verify: AC-1: dual-core filename contains Cc2 (2 cores)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: dual-core filename contains Cc2 (2 cores)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = make_dual_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Cc2")
```

</details>

#### AC-1: filename contains Iw64 (64-bit instruction bus)

- Verify: AC-1: filename contains Iw64 (64-bit instruction bus)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: filename contains Iw64 (64-bit instruction bus)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Iw64")
```

</details>

#### AC-1: filename contains Dw64 (64-bit data bus)

- Verify: AC-1: filename contains Dw64 (64-bit data bus)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: filename contains Dw64 (64-bit data bus)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Dw64")
```

</details>

#### AC-1: filename contains Ldw128 (128-bit LiteDRAM interface)

- Verify: AC-1: filename contains Ldw128 (128-bit LiteDRAM interface)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: filename contains Ldw128 (128-bit LiteDRAM interface)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_contain("Ldw128")
```

</details>

#### AC-1: filename ends with .v

- Verify: AC-1: filename ends with .v


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: filename ends with .v")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val cfg = make_single_core_config()
val name = vexriscv_smp_v_filename(cfg)
expect(name).to_end_with(".v")
```

</details>

### vexriscv_smp_import_path

#### AC-1: import path is non-empty

- Verify: AC-1: import path is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: import path is non-empty")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val p = vexriscv_smp_import_path()
val len = p.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-1: import path contains opensource_rtl

- Verify: AC-1: import path contains opensource_rtl


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: import path contains opensource_rtl")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val p = vexriscv_smp_import_path()
expect(p).to_contain("opensource_rtl")
```

</details>

#### AC-1: import path contains vexriscv_smp

- Verify: AC-1: import path contains vexriscv_smp


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-1
step("Verify: AC-1: import path contains vexriscv_smp")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0da083a297655a0fb1eed9de5125feaa468ac22ee0007ebda7301a10ca0ee92f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0da083a297655a0fb1eed9de5125feaa468ac22ee0007ebda7301a10ca0ee92f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0da083a297655a0fb1eed9de5125feaa468ac22ee0007ebda7301a10ca0ee92f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/opensource_rtl/vexriscv_smp/vexriscv_smp_import_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
