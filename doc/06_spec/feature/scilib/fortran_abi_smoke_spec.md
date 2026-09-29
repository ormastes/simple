# fortran_abi_smoke_spec

> Purpose: Verify fortran_abi smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fortran_abi_smoke_spec

Purpose: Verify fortran_abi smoke.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/scilib/fortran_abi_smoke_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify fortran_abi smoke.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### fortran_abi smoke

#### LP64 helpers return expected values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- LP64 helpers return expected values
- LP64 helpers return expected values
   - Expected: fortran_int_bytes() equals `8`
   - Expected: fortran_int_is_lp64() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("LP64 helpers return expected values")
step("LP64 helpers return expected values")
# @req: REQ-FEAT-SCILIB-FORTRAN-ABI-SMOKE-SPEC-001
expect(fortran_int_bytes()).to_equal(8)
expect(fortran_int_is_lp64()).to_equal(true)
```

</details>

#### index converters are correct

- index converters are correct
- index converters are correct
   - Expected: rc_to_rm_index(1, 2, 4) equals `6`
   - Expected: rc_to_cm_index(1, 2, 3) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("index converters are correct")
step("index converters are correct")
expect(rc_to_rm_index(1, 2, 4)).to_equal(6)
expect(rc_to_cm_index(1, 2, 3)).to_equal(7)
```

</details>

#### symbol names are canonical

- symbol names are canonical
- symbol names are canonical
   - Expected: blas_symbol_name("gemm", "d") equals `rt_blas_dgemm`
   - Expected: lapack_symbol_name("gesv") equals `rt_lapack_dgesv`
   - Expected: cuda_symbol_name("malloc") equals `rt_cuda_malloc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("symbol names are canonical")
step("symbol names are canonical")
expect(blas_symbol_name("gemm", "d")).to_equal("rt_blas_dgemm")
expect(lapack_symbol_name("gesv")).to_equal("rt_lapack_dgesv")
expect(cuda_symbol_name("malloc")).to_equal("rt_cuda_malloc")
```

</details>

#### operand swap needed for row-major layout

- operand swap needed for row-major layout
- operand swap needed for row-major layout
   - Expected: operand_swap_needed(LAYOUT_ROW_MAJOR) is true
   - Expected: operand_swap_needed(LAYOUT_COL_MAJOR) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("operand swap needed for row-major layout")
step("operand swap needed for row-major layout")
expect(operand_swap_needed(LAYOUT_ROW_MAJOR)).to_equal(true)
expect(operand_swap_needed(LAYOUT_COL_MAJOR)).to_equal(false)
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

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-SCILIB-FORTRAN-ABI-SMOKE-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `70d0d698303eea871b8ecdf128b0cf623e924a8d13e50a496d23387337868552`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70d0d698303eea871b8ecdf128b0cf623e924a8d13e50a496d23387337868552`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70d0d698303eea871b8ecdf128b0cf623e924a8d13e50a496d23387337868552`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/scilib/fortran_abi_smoke_spec.spl
mirror: doc/06_spec/feature/scilib/fortran_abi_smoke_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/fortran_abi_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/fortran_abi_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/fortran_abi_smoke_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/fortran_abi_smoke_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LP64 helpers return expected values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/fortran_abi_smoke_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'index converters are correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/fortran_abi_smoke_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'symbol names are canonical' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
