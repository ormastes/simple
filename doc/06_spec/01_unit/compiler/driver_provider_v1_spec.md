# Driver Provider V1 Specification

> Tests covering CompilerDriverV1 coarse provider boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Provider V1 Specification

## Scenarios

### CompilerDriverV1 coarse provider boundary

#### queries the stable scalar-only descriptor

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- queries the stable scalar-only descriptor
   - Expected: result.status equals `SIMPLE_PROVIDER_OK`
   - Expected: result.provided_major equals `1`
   - Expected: result.descriptor_size equals `SIMPLE_COMPILER_DRIVER_V1_DESCRIPTOR_SIZE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("queries the stable scalar-only descriptor")
val result = simple_compiler_driver_query_v1(provider_query(SIMPLE_COMPILER_DRIVER_V1_INTERFACE, 1, 44))
expect(result.status).to_equal(SIMPLE_PROVIDER_OK)
expect(result.provided_major).to_equal(1)
expect(result.descriptor_size).to_equal(SIMPLE_COMPILER_DRIVER_V1_DESCRIPTOR_SIZE)
expect(result.interface_handle).to_be_greater_than(0)
```

</details>

#### fails closed for unknown interfaces, majors, and short requests

- fails closed for unknown interfaces, majors, and short requests
   - Expected: simple_compiler_driver_query_v1(provider_query(99, 1, 44)).status equals `SIMPLE_PROVIDER_INTERFACE_UNKNOWN`
   - Expected: simple_compiler_driver_query_v1(provider_query(SIMPLE_COMPILER_DRIVER_V1_INTERFACE, 2, 44)).status equals `SIMPLE_PROVIDER_MAJOR_UNSUPPORTED`
   - Expected: simple_compiler_driver_query_v1(provider_query(SIMPLE_COMPILER_DRIVER_V1_INTERFACE, 1, 8)).status equals `SIMPLE_PROVIDER_DESCRIPTOR_TOO_SHORT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed for unknown interfaces, majors, and short requests")
expect(simple_compiler_driver_query_v1(provider_query(99, 1, 44)).status).to_equal(SIMPLE_PROVIDER_INTERFACE_UNKNOWN)
expect(simple_compiler_driver_query_v1(provider_query(SIMPLE_COMPILER_DRIVER_V1_INTERFACE, 2, 44)).status).to_equal(SIMPLE_PROVIDER_MAJOR_UNSUPPORTED)
expect(simple_compiler_driver_query_v1(provider_query(SIMPLE_COMPILER_DRIVER_V1_INTERFACE, 1, 8)).status).to_equal(SIMPLE_PROVIDER_DESCRIPTOR_TOO_SHORT)
```

</details>

#### owns sessions, requests, and results behind numeric handles

- owns sessions, requests, and results behind numeric handles
   - Expected: session.status equals `SIMPLE_COMPILER_PROVIDER_OK`
   - Expected: request.status equals `SIMPLE_COMPILER_PROVIDER_OK`
   - Expected: provider.release_session(session.handle) equals `SIMPLE_COMPILER_PROVIDER_SESSION_BUSY`
   - Expected: result.status equals `SIMPLE_COMPILER_PROVIDER_OK`
   - Expected: summary.status equals `SIMPLE_COMPILER_PROVIDER_OK`
   - Expected: summary.compile_status equals `SIMPLE_COMPILER_PROVIDER_COMPILE_FAILED`
   - Expected: provider.run_request(request.handle).status equals `SIMPLE_COMPILER_PROVIDER_REQUEST_ALREADY_RUN`
   - Expected: provider.release_result(result.handle) equals `SIMPLE_COMPILER_PROVIDER_OK`
   - Expected: provider.inspect_result(result.handle).status equals `SIMPLE_COMPILER_PROVIDER_INVALID_RESULT`
   - Expected: provider.release_request(request.handle) equals `SIMPLE_COMPILER_PROVIDER_OK`
   - Expected: provider.release_session(session.handle) equals `SIMPLE_COMPILER_PROVIDER_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("owns sessions, requests, and results behind numeric handles")
var provider = CompilerDriverProviderInProcessV1.create()
val session = provider.create_session(driver_core_compile_options_default())
expect(session.status).to_equal(SIMPLE_COMPILER_PROVIDER_OK)
expect(session.handle).to_be_greater_than(0)
val request = provider.create_request(session.handle)
expect(request.status).to_equal(SIMPLE_COMPILER_PROVIDER_OK)
expect(provider.release_session(session.handle)).to_equal(SIMPLE_COMPILER_PROVIDER_SESSION_BUSY)
val result = provider.run_request(request.handle)
expect(result.status).to_equal(SIMPLE_COMPILER_PROVIDER_OK)
val summary = provider.inspect_result(result.handle)
expect(summary.status).to_equal(SIMPLE_COMPILER_PROVIDER_OK)
expect(summary.compile_status).to_equal(SIMPLE_COMPILER_PROVIDER_COMPILE_FAILED)
expect(summary.diagnostic_count).to_be_greater_than(0)
expect(provider.run_request(request.handle).status).to_equal(SIMPLE_COMPILER_PROVIDER_REQUEST_ALREADY_RUN)
expect(provider.release_result(result.handle)).to_equal(SIMPLE_COMPILER_PROVIDER_OK)
expect(provider.inspect_result(result.handle).status).to_equal(SIMPLE_COMPILER_PROVIDER_INVALID_RESULT)
expect(provider.release_request(request.handle)).to_equal(SIMPLE_COMPILER_PROVIDER_OK)
expect(provider.release_session(session.handle)).to_equal(SIMPLE_COMPILER_PROVIDER_OK)
```

</details>

#### rejects zero and stale handles

- rejects zero and stale handles
   - Expected: provider.create_request(0).status equals `SIMPLE_COMPILER_PROVIDER_INVALID_SESSION`
   - Expected: provider.run_request(0).status equals `SIMPLE_COMPILER_PROVIDER_INVALID_REQUEST`
   - Expected: provider.inspect_result(0).status equals `SIMPLE_COMPILER_PROVIDER_INVALID_RESULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects zero and stale handles")
var provider = CompilerDriverProviderInProcessV1.create()
expect(provider.create_request(0).status).to_equal(SIMPLE_COMPILER_PROVIDER_INVALID_SESSION)
expect(provider.run_request(0).status).to_equal(SIMPLE_COMPILER_PROVIDER_INVALID_REQUEST)
expect(provider.inspect_result(0).status).to_equal(SIMPLE_COMPILER_PROVIDER_INVALID_RESULT)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver_provider_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CompilerDriverV1 coarse provider boundary.
- CompilerDriverV1 coarse provider boundary

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9456241b07d1633656edc93a159b542db6cd03da14af7a0e9208771bf800618f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9456241b07d1633656edc93a159b542db6cd03da14af7a0e9208771bf800618f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9456241b07d1633656edc93a159b542db6cd03da14af7a0e9208771bf800618f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/driver_provider_v1_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver_provider_v1_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver_provider_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver_provider_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver_provider_v1_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver_provider_v1_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'queries the stable scalar-only descriptor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver_provider_v1_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for unknown interfaces, majors, and short requests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver_provider_v1_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owns sessions, requests, and results behind numeric handles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
