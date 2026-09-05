# Simpleos Target V1 Specification

> Tests covering SimpleOS canonical target contract v1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Target V1 Specification

## Scenarios

### SimpleOS canonical target contract v1

#### binds required architecture triples to ABI and firmware profiles

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds required architecture triples to ABI and firmware profiles
   - Expected: simpleos_target_v1_abi_for_triple(SIMPLEOS_TARGET_V1_X86_64_TRIPLE) equals `sysv`
   - Expected: simpleos_target_v1_firmware_for_triple(SIMPLEOS_TARGET_V1_X86_64_TRIPLE) equals `LimineBios`
   - Expected: simpleos_target_v1_abi_for_triple(SIMPLEOS_TARGET_V1_AARCH64_TRIPLE) equals `aapcs64`
   - Expected: simpleos_target_v1_firmware_for_triple(SIMPLEOS_TARGET_V1_AARCH64_TRIPLE) equals `RawLoader`
   - Expected: simpleos_target_v1_abi_for_triple(SIMPLEOS_TARGET_V1_RISCV64GC_TRIPLE) equals `lp64d`
   - Expected: simpleos_target_v1_firmware_for_triple(SIMPLEOS_TARGET_V1_RISCV64GC_TRIPLE) equals `OpenSbi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("binds required architecture triples to ABI and firmware profiles")
expect(simpleos_target_v1_abi_for_triple(SIMPLEOS_TARGET_V1_X86_64_TRIPLE)).to_equal("sysv")
expect(simpleos_target_v1_firmware_for_triple(SIMPLEOS_TARGET_V1_X86_64_TRIPLE)).to_equal("LimineBios")
expect(simpleos_target_v1_abi_for_triple(SIMPLEOS_TARGET_V1_AARCH64_TRIPLE)).to_equal("aapcs64")
expect(simpleos_target_v1_firmware_for_triple(SIMPLEOS_TARGET_V1_AARCH64_TRIPLE)).to_equal("RawLoader")
expect(simpleos_target_v1_abi_for_triple(SIMPLEOS_TARGET_V1_RISCV64GC_TRIPLE)).to_equal("lp64d")
expect(simpleos_target_v1_firmware_for_triple(SIMPLEOS_TARGET_V1_RISCV64GC_TRIPLE)).to_equal("OpenSbi")
```

</details>

#### rejects unknown triples without inferring a host target

- rejects unknown triples without inferring a host target
   - Expected: simpleos_target_v1_is_userland_triple("mips64-unknown-simpleos") is false
   - Expected: simpleos_target_v1_abi_for_triple("mips64-unknown-simpleos") equals ``
   - Expected: simpleos_target_v1_firmware_for_triple("mips64-unknown-simpleos") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unknown triples without inferring a host target")
expect(simpleos_target_v1_is_userland_triple("mips64-unknown-simpleos")).to_equal(false)
expect(simpleos_target_v1_abi_for_triple("mips64-unknown-simpleos")).to_equal("")
expect(simpleos_target_v1_firmware_for_triple("mips64-unknown-simpleos")).to_equal("")
```

</details>

#### publishes a duplicate-free nonempty canonical catalog

- publishes a duplicate-free nonempty canonical catalog
   - Expected: triples.len() equals `6`
   - Expected: triples[i].trim() == "" is false
   - Expected: triples[i] == triples[j] is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("publishes a duplicate-free nonempty canonical catalog")
val triples = simpleos_target_v1_canonical_triples()
expect(triples.len()).to_equal(6)
var i = 0
while i < triples.len():
    expect(triples[i].trim() == "").to_equal(false)
    var j = i + 1
    while j < triples.len():
        expect(triples[i] == triples[j]).to_equal(false)
        j = j + 1
    i = i + 1
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/contracts/execution/simpleos_target_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS canonical target contract v1.
- SimpleOS canonical target contract v1

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

- `REQ-SSPEC-UNIT`
- `REQ-002`
- `REQ-009`
- `REQ-010`
- `REQ-011`
- `REQ-019`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f3fb93f8af95516f55d353e598bf69281cb6e5a41c4a0f72f805b3283aeba6c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3fb93f8af95516f55d353e598bf69281cb6e5a41c4a0f72f805b3283aeba6c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3fb93f8af95516f55d353e598bf69281cb6e5a41c4a0f72f805b3283aeba6c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/contracts/execution/simpleos_target_v1_spec.spl
mirror: doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_target_v1_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_target_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/contracts/execution/simpleos_target_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/contracts/execution/simpleos_target_v1_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/contracts/execution/simpleos_target_v1_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 6 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/contracts/execution/simpleos_target_v1_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds required architecture triples to ABI and firmware profiles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/execution/simpleos_target_v1_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unknown triples without inferring a host target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/execution/simpleos_target_v1_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes a duplicate-free nonempty canonical catalog' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
