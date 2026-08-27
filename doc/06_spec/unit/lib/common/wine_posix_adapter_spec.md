# Wine Posix Adapter Specification

> Tests covering Wine POSIX adapter contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Posix Adapter Specification

## Scenarios

### Wine POSIX adapter contract

#### lists fd, process, stdio, wait, timer, socket, path, and errno APIs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lists fd, process, stdio, wait, timer, socket, path, and errno APIs
   - Expected: apis[0] equals `fd-open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists fd, process, stdio, wait, timer, socket, path, and errno APIs")
val apis = wine_posix_adapter_required_apis()
expect(apis.len()).to_be_greater_than(15)
expect(apis[0]).to_equal("fd-open")
```

</details>

#### reports the first missing adapter API

- reports the first missing adapter API
   - Expected: missing[0] equals `fd-dup`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the first missing adapter API")
val missing = wine_posix_adapter_missing_apis("fd-open fd-read fd-write fd-close")
expect(missing[0]).to_equal("fd-dup")
```

</details>

#### maps blocking-compatible adapter APIs onto nogc async primitives

- maps blocking-compatible adapter APIs onto nogc async primitives
   - Expected: wine_posix_adapter_async_binding("fd-read") equals `submit-read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps blocking-compatible adapter APIs onto nogc async primitives")
expect(wine_posix_adapter_async_binding("fd-read")).to_equal("submit-read")
expect(wine_posix_adapter_async_binding("poll-wait")).to_contain("register-fd")
expect(wine_posix_adapter_async_binding("socket")).to_contain("event-loop")
```

</details>

#### derives POSIX gate features from concrete adapter APIs

- derives POSIX gate features from concrete adapter APIs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives POSIX gate features from concrete adapter APIs")
val features = wine_posix_adapter_feature_string(_all_adapter_apis())
expect(features).to_contain("fd-table")
expect(features).to_contain("cwd-env-argv")
expect(features).to_contain("spawn")
```

</details>

#### blocks readiness when async completion polling is missing

- blocks readiness when async completion polling is missing
   - Expected: result.ready is false
   - Expected: result.state equals `blocked-async-io:missing-poll-completion`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("blocks readiness when async completion polling is missing")
val result = wine_posix_adapter_gate(_all_adapter_apis(), "io-driver submit-open submit-read submit-write submit-close submit-timeout")
expect(result.ready).to_equal(false)
expect(result.state).to_equal("blocked-async-io:missing-poll-completion")
```

</details>

#### accepts the full adapter API set on a nogc async backend

- accepts the full adapter API set on a nogc async backend
   - Expected: result.ready is true
   - Expected: result.state equals `ready`
   - Expected: result.async_state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts the full adapter API set on a nogc async backend")
val result = wine_posix_adapter_gate(_all_adapter_apis(), _all_async_features())
expect(result.ready).to_equal(true)
expect(result.state).to_equal("ready")
expect(result.async_state).to_equal("ready")
```

</details>

#### requires bounded KERNEL32 file I/O evidence before full adapter readiness

- requires bounded KERNEL32 file I/O evidence before full adapter readiness
   - Expected: result.ready is true
   - Expected: result.state equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires bounded KERNEL32 file I/O evidence before full adapter readiness")
val file_result = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "CloseHandle"], _table_with_file(), "C:\\hello.txt", 5)
val result = wine_posix_adapter_gate_with_file_io_result(_all_adapter_apis(), _all_async_features(), file_result)
expect(result.ready).to_equal(true)
expect(result.state).to_equal("ready")
expect(result.posix_features).to_contain("kernel32-file-io")
```

</details>

#### keeps POSIX readiness blocked on failed file I/O bridge evidence

- keeps POSIX readiness blocked on failed file I/O bridge evidence
   - Expected: result.ready is false
   - Expected: result.state equals `file-io-CreateFileW:file-not-found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps POSIX readiness blocked on failed file I/O bridge evidence")
val file_result = wine_kernel32_execute_file_io(["CreateFileW", "ReadFile", "GetFileType", "CloseHandle"], _table_with_file(), "C:\\missing.txt", 5)
val result = wine_posix_adapter_gate_with_file_io_result(_all_adapter_apis(), _all_async_features(), file_result)
expect(result.ready).to_equal(false)
expect(result.state).to_equal("file-io-CreateFileW:file-not-found")
```

</details>

#### normalizes host errno values used by Wine compatibility shims

- normalizes host errno values used by Wine compatibility shims
   - Expected: wine_posix_adapter_errno_name(2) equals `ENOENT`
   - Expected: wine_posix_adapter_errno_name(11) equals `EAGAIN`
   - Expected: wine_posix_adapter_errno_name(9999) equals `EUNKNOWN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes host errno values used by Wine compatibility shims")
expect(wine_posix_adapter_errno_name(2)).to_equal("ENOENT")
expect(wine_posix_adapter_errno_name(11)).to_equal("EAGAIN")
expect(wine_posix_adapter_errno_name(9999)).to_equal("EUNKNOWN")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_posix_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine POSIX adapter contract.
- Wine POSIX adapter contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `a01caf80efad03ef1a929657dc236f2be3dd729e1071fd7964aa9760a69cea43`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a01caf80efad03ef1a929657dc236f2be3dd729e1071fd7964aa9760a69cea43`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a01caf80efad03ef1a929657dc236f2be3dd729e1071fd7964aa9760a69cea43`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/wine_posix_adapter_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_posix_adapter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_posix_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_posix_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_posix_adapter_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists fd, process, stdio, wait, timer, socket, path, and errno APIs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_posix_adapter_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the first missing adapter API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_posix_adapter_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps blocking-compatible adapter APIs onto nogc async primitives' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
