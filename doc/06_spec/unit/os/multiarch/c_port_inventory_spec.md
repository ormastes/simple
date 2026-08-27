# C Port Inventory Specification

> Tests covering AC-1 — C → Simple inventory artefact, AC-2 — zero owned-code .c compiles for SimpleOS, AC-1/AC-2 cross-link to architecture doc.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# C Port Inventory Specification

## Scenarios

### AC-1 — C → Simple inventory artefact

#### inventory file exists

- inventory file exists
   - Expected: file_exists(INVENTORY_PATH) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inventory file exists")
expect(file_exists(INVENTORY_PATH)).to_equal(true)
```

</details>

#### inventory file is non-empty

- inventory file is non-empty
   - Expected: body.length() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inventory file is non-empty")
val body: text = file_read(INVENTORY_PATH)
expect(body.length() > 0).to_equal(true)
```

</details>

#### inventory lists the runtime_minimal critical-path entry

- inventory lists the runtime_minimal critical-path entry
   - Expected: body contains `runtime_minimal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inventory lists the runtime_minimal critical-path entry")
"""Phase 2 inventory must call out runtime_minimal.c (246 LoC,
Wave 1 port target) by name."""
val body: text = file_read(INVENTORY_PATH)
expect(body.contains("runtime_minimal")).to_equal(true)
```

</details>

#### inventory lists simpleos_crt0 and simpleos_setjmp

- inventory lists simpleos_crt0 and simpleos_setjmp
   - Expected: body contains `simpleos_crt0`
   - Expected: body contains `simpleos_setjmp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inventory lists simpleos_crt0 and simpleos_setjmp")
"""The two assembly files HalCstart will replace must appear in
the inventory so the port map is auditable."""
val body: text = file_read(INVENTORY_PATH)
expect(body.contains("simpleos_crt0")).to_equal(true)
expect(body.contains("simpleos_setjmp")).to_equal(true)
```

</details>

#### inventory documents the EXCLUDED vendor + bootstrap allow-list

- inventory documents the EXCLUDED vendor + bootstrap allow-list
   - Expected: body contains `vendor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inventory documents the EXCLUDED vendor + bootstrap allow-list")
"""AC-2 says residual C is restricted to vendor + 3 bootstrap
scripts only. The inventory must say so explicitly."""
val body: text = file_read(INVENTORY_PATH)
expect(body.contains("vendor")).to_equal(true)
```

</details>

### AC-2 — zero owned-code .c compiles for SimpleOS

#### owned-C compile report exists after a SimpleOS build

- owned-C compile report exists after a SimpleOS build
   - Expected: file_exists(OWNED_C_REPORT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("owned-C compile report exists after a SimpleOS build")
"""RED today: the build does not yet emit this report. Phase 5
wires the manifest writer into qemu_runner.spl."""
expect(file_exists(OWNED_C_REPORT)).to_equal(true)
```

</details>

#### owned-C report shows zero entries outside the allow-list

- owned-C report shows zero entries outside the allow-list
   - Expected: report contains `"violations": []`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("owned-C report shows zero entries outside the allow-list")
val report: text = file_read(OWNED_C_REPORT)
expect(report.contains("\"violations\": []")).to_equal(true)
```

</details>

#### report explicitly names the documented allow-list paths

- report explicitly names the documented allow-list paths
   - Expected: report contains `vendor`
   - Expected: report contains `miniaudio`
   - Expected: report contains `stb_image`
   - Expected: report contains `stb_truetype`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("report explicitly names the documented allow-list paths")
"""Allow-list members per architecture §3 + CLAUDE.md:
src/compiler_rust/vendor, src/runtime/vendor,
runtime/miniaudio.h, runtime/stb_image.h, runtime/stb_truetype.h,
and the 3 bootstrap shell scripts."""
val report: text = file_read(OWNED_C_REPORT)
expect(report.contains("vendor")).to_equal(true)
expect(report.contains("miniaudio")).to_equal(true)
expect(report.contains("stb_image")).to_equal(true)
expect(report.contains("stb_truetype")).to_equal(true)
```

</details>

#### no new owned .c file appears outside the locked allow-list

- no new owned .c file appears outside the locked allow-list
   - Expected: report contains `"residual_c_count": 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no new owned .c file appears outside the locked allow-list")
"""Regression guard: scripts/audit/arch_loc_report.shs writes
scan results; the residual_c key must equal the locked count."""
val report: text = file_read(OWNED_C_REPORT)
expect(report.contains("\"residual_c_count\": 0")).to_equal(true)
```

</details>

### AC-1/AC-2 cross-link to architecture doc

#### architecture doc references the inventory file

- architecture doc references the inventory file
   - Expected: body contains `c_to_simple_inventory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("architecture doc references the inventory file")
val body: text = file_read(ARCH_DOC_PATH)
expect(body.contains("c_to_simple_inventory")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/multiarch/c_port_inventory_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AC-1 — C → Simple inventory artefact, AC-2 — zero owned-code .c compiles for SimpleOS, AC-1/AC-2 cross-link to architecture doc.
- AC-1 — C → Simple inventory artefact
- AC-2 — zero owned-code .c compiles for SimpleOS
- AC-1/AC-2 cross-link to architecture doc

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `440aa98e366528cfe5e75d406038f0beb423b697ed11ef2a17e19c4fd34453e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `440aa98e366528cfe5e75d406038f0beb423b697ed11ef2a17e19c4fd34453e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `440aa98e366528cfe5e75d406038f0beb423b697ed11ef2a17e19c4fd34453e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/multiarch/c_port_inventory_spec.spl
mirror: doc/06_spec/unit/os/multiarch/c_port_inventory_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/multiarch/c_port_inventory_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/multiarch/c_port_inventory_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/multiarch/c_port_inventory_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inventory file exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/multiarch/c_port_inventory_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inventory file is non-empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/multiarch/c_port_inventory_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inventory lists the runtime_minimal critical-path entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
