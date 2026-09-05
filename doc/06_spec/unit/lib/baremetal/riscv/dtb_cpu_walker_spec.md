# Dtb Cpu Walker Specification

> Tests covering DTB CPU Walker, count_okay_cpus — valid FDT, count_okay_cpus — status=disabled filter, count_okay_cpus — missing or invalid DTB, cached_cbom_block_size — from DTB riscv,cbom-block-size property, cached_isa_string — Zicbom substring detection, memoization — dtb_scan_init is idempotent.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dtb Cpu Walker Specification

## Scenarios

### DTB CPU Walker

### count_okay_cpus — valid FDT

#### AC-1: returns 1 for single hart with no status (defaults to okay)

- AC-1: returns 1 for single hart with no status (defaults to okay)
   - Expected: count equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns 1 for single hart with no status (defaults to okay)")
val harts = [HartDesc(id: 0u32, status: "", isa: "rv64gc")]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
val count = cached_cpu_count()
expect(count).to_equal(1u32)
```

</details>

#### AC-1: returns 2 for two harts both status=okay

- AC-1: returns 2 for two harts both status=okay
   - Expected: count equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns 2 for two harts both status=okay")
val harts = [
    HartDesc(id: 0u32, status: "okay", isa: "rv64gc"),
    HartDesc(id: 1u32, status: "okay", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
val count = cached_cpu_count()
expect(count).to_equal(2u32)
```

</details>

#### AC-1: returns 4 for four-hart SMP FDT

- AC-1: returns 4 for four-hart SMP FDT
   - Expected: cached_cpu_count() equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns 4 for four-hart SMP FDT")
val harts = [
    HartDesc(id: 0u32, status: "okay", isa: "rv64gc"),
    HartDesc(id: 1u32, status: "okay", isa: "rv64gc"),
    HartDesc(id: 2u32, status: "okay", isa: "rv64gc"),
    HartDesc(id: 3u32, status: "okay", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
expect(cached_cpu_count()).to_equal(4u32)
```

</details>

### count_okay_cpus — status=disabled filter

#### AC-1: excludes hart with status=disabled

- AC-1: excludes hart with status=disabled
   - Expected: cached_cpu_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: excludes hart with status=disabled")
val harts = [
    HartDesc(id: 0u32, status: "okay", isa: "rv64gc"),
    HartDesc(id: 1u32, status: "disabled", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
expect(cached_cpu_count()).to_equal(1u32)
```

</details>

#### AC-1: all disabled harts returns fallback of 1

- AC-1: all disabled harts returns fallback of 1
   - Expected: cached_cpu_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: all disabled harts returns fallback of 1")
val harts = [
    HartDesc(id: 0u32, status: "disabled", isa: "rv64gc"),
    HartDesc(id: 1u32, status: "disabled", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
expect(cached_cpu_count()).to_equal(1u32)
```

</details>

### count_okay_cpus — missing or invalid DTB

#### AC-1: null FDT pointer returns fallback of 1

- AC-1: null FDT pointer returns fallback of 1
   - Expected: cached_cpu_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: null FDT pointer returns fallback of 1")
dtb_scan_init_from_bytes(make_fdt_null())
expect(cached_cpu_count()).to_equal(1u32)
```

</details>

#### AC-1: bad magic returns fallback of 1

- AC-1: bad magic returns fallback of 1
   - Expected: cached_cpu_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: bad magic returns fallback of 1")
dtb_scan_init_from_bytes(make_fdt_bad_magic())
expect(cached_cpu_count()).to_equal(1u32)
```

</details>

### cached_cbom_block_size — from DTB riscv,cbom-block-size property

#### AC-5: returns DTB-advertised block size when present

- AC-5: returns DTB-advertised block size when present


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: returns DTB-advertised block size when present")
val harts = [HartDesc(id: 0u32, status: "okay", isa: "rv64gc_zicbom")]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
val sz = cached_cbom_block_size()
expect(sz).to_be_greater_than(0u32)
```

</details>

#### AC-5: returns default 64 when DTB has no riscv,cbom-block-size

- AC-5: returns default 64 when DTB has no riscv,cbom-block-size
   - Expected: cached_cbom_block_size() equals `64u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: returns default 64 when DTB has no riscv,cbom-block-size")
val harts = [HartDesc(id: 0u32, status: "okay", isa: "rv64gc")]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
expect(cached_cbom_block_size()).to_equal(64u32)
```

</details>

### cached_isa_string — Zicbom substring detection

#### AC-3: isa string containing _zicbom signals Zicbom support

- AC-3: isa string containing _zicbom signals Zicbom support


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: isa string containing _zicbom signals Zicbom support")
val harts = [HartDesc(id: 0u32, status: "okay", isa: "rv64gc_zicbom_zicboz")]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
val isa = cached_isa_string(0u32)
expect(isa).to_contain("_zicbom")
```

</details>

#### AC-3: isa string without _zicbom correctly absent

- AC-3: isa string without _zicbom correctly absent
   - Expected: isa equals `rv64gc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-3: isa string without _zicbom correctly absent")
val harts = [HartDesc(id: 0u32, status: "okay", isa: "rv64gc")]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
val isa = cached_isa_string(0u32)
expect(isa).to_equal("rv64gc")
```

</details>

### memoization — dtb_scan_init is idempotent

#### AC-1: second call with same blob does not change cached count

- AC-1: second call with same blob does not change cached count
   - Expected: count_second equals `count_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: second call with same blob does not change cached count")
val harts = [
    HartDesc(id: 0u32, status: "okay", isa: "rv64gc"),
    HartDesc(id: 1u32, status: "okay", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus(harts)
dtb_scan_init_from_bytes(fdt)
val count_first = cached_cpu_count()
dtb_scan_init_from_bytes(fdt)
val count_second = cached_cpu_count()
expect(count_second).to_equal(count_first)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/baremetal/riscv/dtb_cpu_walker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DTB CPU Walker, count_okay_cpus — valid FDT, count_okay_cpus — status=disabled filter, count_okay_cpus — missing or invalid DTB, cached_cbom_block_size — from DTB riscv,cbom-block-size property, cached_isa_string — Zicbom substring detection, memoization — dtb_scan_init is idempotent.
- DTB CPU Walker
- count_okay_cpus — valid FDT
- count_okay_cpus — status=disabled filter
- count_okay_cpus — missing or invalid DTB
- cached_cbom_block_size — from DTB riscv,cbom-block-size property
- cached_isa_string — Zicbom substring detection
- memoization — dtb_scan_init is idempotent

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `23c6ead74f3f3c62229afa95f59f6fb5585a5e6ecaa3b55818622d056edfd898`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `23c6ead74f3f3c62229afa95f59f6fb5585a5e6ecaa3b55818622d056edfd898`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `23c6ead74f3f3c62229afa95f59f6fb5585a5e6ecaa3b55818622d056edfd898`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/baremetal/riscv/dtb_cpu_walker_spec.spl
mirror: doc/06_spec/unit/lib/baremetal/riscv/dtb_cpu_walker_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/baremetal/riscv/dtb_cpu_walker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/baremetal/riscv/dtb_cpu_walker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/baremetal/riscv/dtb_cpu_walker_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: returns 1 for single hart with no status (defaults to okay)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/baremetal/riscv/dtb_cpu_walker_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: returns 2 for two harts both status=okay' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/baremetal/riscv/dtb_cpu_walker_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: returns 4 for four-hart SMP FDT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
