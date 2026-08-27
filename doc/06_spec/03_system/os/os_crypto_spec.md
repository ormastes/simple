# Os Crypto Specification

> Tests covering OS crypto RFC test vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Crypto Specification

## Scenarios

### OS crypto RFC test vectors

#### passes every SHA-256/HMAC/AES-GCM/ChaCha20/Poly1305/X25519/Ed25519 vector

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- run the full RFC vector harness and require zero failures
   - Expected: _fail_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("run the full RFC vector harness and require zero failures")
os_crypto_test()
# oracle: _fail_count is incremented by _assert on every failed vector check
expect(_fail_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_crypto_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering OS crypto RFC test vectors.
- OS crypto RFC test vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `c9ab3cb38d496cfa446962d095a98dae6b303b5bfeb8fad20b867f80815e002f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c9ab3cb38d496cfa446962d095a98dae6b303b5bfeb8fad20b867f80815e002f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c9ab3cb38d496cfa446962d095a98dae6b303b5bfeb8fad20b867f80815e002f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/03_system/os/os_crypto_spec.spl
mirror: doc/06_spec/03_system/os/os_crypto_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/os_crypto_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/os_crypto_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/os_crypto_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/os_crypto_spec.spl:804:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes every SHA-256/HMAC/AES-GCM/ChaCha20/Poly1305/X25519/Ed25519 vector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
