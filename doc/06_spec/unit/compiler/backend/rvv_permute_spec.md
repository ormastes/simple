# Rvv Permute Specification

> Tests covering RVV vslideup/vslidedown byte-level emit, RVV vrgather byte-level emit, RVV permute output properties.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rvv Permute Specification

## Scenarios

### RVV vslideup/vslidedown byte-level emit

#### vslideup.vx v0, v0, x0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- vslideup.vx v0, v0, x0
   - Expected: _list_hex(emit_rvv_vslideup_vx(0, 0, 0)) equals `5740003a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vslideup.vx v0, v0, x0")
expect(_list_hex(emit_rvv_vslideup_vx(0, 0, 0))).to_equal("5740003a")
```

</details>

#### vslidedown.vx v0, v0, x0

- vslidedown.vx v0, v0, x0
   - Expected: _list_hex(emit_rvv_vslidedown_vx(0, 0, 0)) equals `5740003e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vslidedown.vx v0, v0, x0")
expect(_list_hex(emit_rvv_vslidedown_vx(0, 0, 0))).to_equal("5740003e")
```

</details>

#### vslide1up.vx v0, v0, x0

- vslide1up.vx v0, v0, x0
   - Expected: _list_hex(emit_rvv_vslide1up_vx(0, 0, 0)) equals `5760003a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vslide1up.vx v0, v0, x0")
expect(_list_hex(emit_rvv_vslide1up_vx(0, 0, 0))).to_equal("5760003a")
```

</details>

#### vslide1down.vx v0, v0, x0

- vslide1down.vx v0, v0, x0
   - Expected: _list_hex(emit_rvv_vslide1down_vx(0, 0, 0)) equals `5760003e`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vslide1down.vx v0, v0, x0")
expect(_list_hex(emit_rvv_vslide1down_vx(0, 0, 0))).to_equal("5760003e")
```

</details>

#### vslideup.vx v1, v2, x3 (non-zero regs)

- vslideup.vx v1, v2, x3 (non-zero regs)
   - Expected: _list_hex(emit_rvv_vslideup_vx(1, 2, 3)) equals `d7c0213a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vslideup.vx v1, v2, x3 (non-zero regs)")
expect(_list_hex(emit_rvv_vslideup_vx(1, 2, 3))).to_equal("d7c0213a")
```

</details>

### RVV vrgather byte-level emit

#### vrgather.vv v0, v0, v0

- vrgather.vv v0, v0, v0
   - Expected: _list_hex(emit_rvv_vrgather_vv(0, 0, 0)) equals `57000032`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vrgather.vv v0, v0, v0")
expect(_list_hex(emit_rvv_vrgather_vv(0, 0, 0))).to_equal("57000032")
```

</details>

#### vrgather.vx v0, v0, x0

- vrgather.vx v0, v0, x0
   - Expected: _list_hex(emit_rvv_vrgather_vx(0, 0, 0)) equals `57400032`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vrgather.vx v0, v0, x0")
expect(_list_hex(emit_rvv_vrgather_vx(0, 0, 0))).to_equal("57400032")
```

</details>

#### vrgather.vv vs vrgather.vx differ in byte[1] (funct3)

- vrgather.vv vs vrgather.vx differ in byte[1] (funct3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vrgather.vv vs vrgather.vx differ in byte[1] (funct3)")
val vv = emit_rvv_vrgather_vv(0, 0, 0)
val vx = emit_rvv_vrgather_vx(0, 0, 0)
expect(vv[1]).to_not_equal(vx[1])
```

</details>

### RVV permute output properties

#### all outputs are 4 bytes

- all outputs are 4 bytes
   - Expected: emit_rvv_vslideup_vx(0, 0, 0).len() equals `4`
   - Expected: emit_rvv_vrgather_vv(0, 0, 0).len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all outputs are 4 bytes")
expect(emit_rvv_vslideup_vx(0, 0, 0).len()).to_equal(4)
expect(emit_rvv_vrgather_vv(0, 0, 0).len()).to_equal(4)
```

</details>

#### slideup vs slidedown differ only in byte[3] high bits

- slideup vs slidedown differ only in byte[3] high bits
   - Expected: up[0] equals `dn[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slideup vs slidedown differ only in byte[3] high bits")
val up = emit_rvv_vslideup_vx(0, 0, 0)
val dn = emit_rvv_vslidedown_vx(0, 0, 0)
expect(up[0]).to_equal(dn[0])
expect(up[3]).to_not_equal(dn[3])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/rvv_permute_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RVV vslideup/vslidedown byte-level emit, RVV vrgather byte-level emit, RVV permute output properties.
- RVV vslideup/vslidedown byte-level emit
- RVV vrgather byte-level emit
- RVV permute output properties

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

- Canonical SPipe generation for source `34ab5b91d387b73681f9cd1246b69915676b786aced04f5916a9b78313886bec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `34ab5b91d387b73681f9cd1246b69915676b786aced04f5916a9b78313886bec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `34ab5b91d387b73681f9cd1246b69915676b786aced04f5916a9b78313886bec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/backend/rvv_permute_spec.spl
mirror: doc/06_spec/unit/compiler/backend/rvv_permute_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/rvv_permute_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/rvv_permute_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/rvv_permute_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/rvv_permute_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'vslideup.vx v0, v0, x0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/rvv_permute_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'vslidedown.vx v0, v0, x0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/rvv_permute_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'vslide1up.vx v0, v0, x0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
