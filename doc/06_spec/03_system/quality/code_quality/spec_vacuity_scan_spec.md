# Spec Vacuity Scan Specification

> Tests covering spec_vacuity_scan — bare assert detection, spec_vacuity_scan — zero-assertion it blocks, spec_vacuity_scan — comma-shape tripwire (3695df74c59 crash class).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spec Vacuity Scan Specification

## Scenarios

### spec_vacuity_scan — bare assert detection

#### flags a bare `assert <cond>` line

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- flags a bare `assert <cond>` line
   - Expected: r.bare_asserts.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flags a bare `assert <cond>` line")
val src = "describe \"x\":\n    it \"y\":\n        assert 1 == 2\n"
val r = scan_file_content("f.spl", src)
expect(r.bare_asserts.len()).to_equal(1)
```

</details>

#### does not flag assert(...) paren-call form

- does not flag assert(...) paren-call form
   - Expected: r.bare_asserts.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag assert(...) paren-call form")
val src = "it \"y\":\n    assert(1 == 1)\n"
val r = scan_file_content("f.spl", src)
expect(r.bare_asserts.len()).to_equal(0)
```

</details>

#### does not flag assert_true(...)

- does not flag assert_true(...)
   - Expected: r.bare_asserts.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag assert_true(...)")
val src = "it \"y\":\n    assert_true(true)\n"
val r = scan_file_content("f.spl", src)
expect(r.bare_asserts.len()).to_equal(0)
```

</details>

#### does not flag assert!(...) macro form

- does not flag assert!(...) macro form
   - Expected: r.bare_asserts.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag assert!(...) macro form")
val src = "it \"y\":\n    assert!(true)\n"
val r = scan_file_content("f.spl", src)
expect(r.bare_asserts.len()).to_equal(0)
```

</details>

### spec_vacuity_scan — zero-assertion it blocks

#### flags an it block with no assertion call at all

- flags an it block with no assertion call at all
   - Expected: r.it_blocks_scanned equals `1`
   - Expected: r.empty_it_blocks.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flags an it block with no assertion call at all")
val src = "describe \"x\":\n    it \"does nothing\":\n        val a = 1\n"
val r = scan_file_content("f.spl", src)
expect(r.it_blocks_scanned).to_equal(1)
expect(r.empty_it_blocks.len()).to_equal(1)
```

</details>

#### does not flag an it block using expect(...)

- does not flag an it block using expect(...)
   - Expected: r.empty_it_blocks.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag an it block using expect(...)")
val src = "describe \"x\":\n    it \"checks\":\n        expect(1).to_equal(1)\n"
val r = scan_file_content("f.spl", src)
expect(r.empty_it_blocks.len()).to_equal(0)
```

</details>

#### does not flag an it block using an expect_* helper (expect_not regression)

- does not flag an it block using an expect_* helper (expect_not regression)
   - Expected: r.empty_it_blocks.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag an it block using an expect_* helper (expect_not regression)")
val src = "describe \"x\":\n    it \"checks\":\n        expect_not(false)\n"
val r = scan_file_content("f.spl", src)
expect(r.empty_it_blocks.len()).to_equal(0)
```

</details>

#### does not flag an it block using assert_true

- does not flag an it block using assert_true
   - Expected: r.empty_it_blocks.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag an it block using assert_true")
val src = "describe \"x\":\n    it \"checks\":\n        assert_true(true)\n"
val r = scan_file_content("f.spl", src)
expect(r.empty_it_blocks.len()).to_equal(0)
```

</details>

### spec_vacuity_scan — comma-shape tripwire (3695df74c59 crash class)

#### flags describe \

- flags describe \
   - Expected: r.comma_shape_hits.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flags describe \")
val src = "describe \"x\", fn():\n    it \"y\":\n        assert_true(true)\n"
val r = scan_file_content("f.spl", src)
expect(r.comma_shape_hits.len()).to_equal(1)
```

</details>

#### flags it \

- flags it \
   - Expected: r.comma_shape_hits.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flags it \")
val src = "describe \"x\":\n    it \"y\", fn():\n        assert_true(true)\n"
val r = scan_file_content("f.spl", src)
expect(r.comma_shape_hits.len()).to_equal(1)
```

</details>

#### does not flag a plain describe \

- does not flag a plain describe \
   - Expected: r.comma_shape_hits.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not flag a plain describe \")
val src = "describe \"x\":\n    it \"y\":\n        assert_true(true)\n"
val r = scan_file_content("f.spl", src)
expect(r.comma_shape_hits.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/spec_vacuity_scan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering spec_vacuity_scan — bare assert detection, spec_vacuity_scan — zero-assertion it blocks, spec_vacuity_scan — comma-shape tripwire (3695df74c59 crash class).
- spec_vacuity_scan — bare assert detection
- spec_vacuity_scan — zero-assertion it blocks
- spec_vacuity_scan — comma-shape tripwire (3695df74c59 crash class)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `25253a7ea95e4b948512eaf66a79eceec272774c2fa0c03bb6609982272eed9f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `25253a7ea95e4b948512eaf66a79eceec272774c2fa0c03bb6609982272eed9f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `25253a7ea95e4b948512eaf66a79eceec272774c2fa0c03bb6609982272eed9f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/quality/code_quality/spec_vacuity_scan_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/spec_vacuity_scan_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/code_quality/spec_vacuity_scan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/spec_vacuity_scan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/spec_vacuity_scan_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/quality/code_quality/spec_vacuity_scan_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a bare `assert <cond>` line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/spec_vacuity_scan_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag assert(...) paren-call form' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/spec_vacuity_scan_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag assert_true(...)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
