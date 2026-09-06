# Tls Ffi Specification

> Tests covering TLS FFI compatibility facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls Ffi Specification

## Scenarios

### TLS FFI compatibility facade

#### contains no duplicate foreign declarations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- contains no duplicate foreign declarations
   - Expected: source does not contain `extern fn `
   - Expected: source does not contain `@extern(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("contains no duplicate foreign declarations")
val source = file_read("src/app/io/tls_ffi.spl")
expect(source.contains("extern fn ")).to_equal(false)
expect(source.contains("@extern(")).to_equal(false)
```

</details>

#### exports the canonical safe TLS surface explicitly

- exports the canonical safe TLS surface explicitly
   - Expected: source contains `tls_connect`
   - Expected: source contains `tls_cert_fingerprint`
   - Expected: source does not contain `tls_sffi.*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("exports the canonical safe TLS surface explicitly")
val source = file_read("src/app/io/tls_ffi.spl")
expect(source).to_contain("export use app.io.tls_sffi.{{")
expect(source.contains("tls_connect")).to_equal(true)
expect(source.contains("tls_cert_fingerprint")).to_equal(true)
expect(source.contains("tls_sffi.*")).to_equal(false)
```

</details>

#### does not re-export raw runtime symbols

- does not re-export raw runtime symbols
   - Expected: source does not contain `rt_rustls_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not re-export raw runtime symbols")
val source = file_read("src/app/io/tls_ffi.spl")
expect(source.contains("rt_rustls_")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/tls_ffi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TLS FFI compatibility facade.
- TLS FFI compatibility facade

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5220cf9206c7f9bbd4c3b86585a2783b07871d9c6888913430e163bacaa1f74d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5220cf9206c7f9bbd4c3b86585a2783b07871d9c6888913430e163bacaa1f74d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5220cf9206c7f9bbd4c3b86585a2783b07871d9c6888913430e163bacaa1f74d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/io/tls_ffi_spec.spl
mirror: doc/06_spec/01_unit/app/io/tls_ffi_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/app/io/tls_ffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/io/tls_ffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/io/tls_ffi_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/io/tls_ffi_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains no duplicate foreign declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/tls_ffi_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports the canonical safe TLS surface explicitly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/tls_ffi_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not re-export raw runtime symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
