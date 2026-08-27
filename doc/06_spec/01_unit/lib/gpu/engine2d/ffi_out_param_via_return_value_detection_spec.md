# Ffi Out Param Via Return Value Detection Specification

> Tests covering GPU FFI out-parameter results are never read from a DynLib return value.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ffi Out Param Via Return Value Detection Specification

## Scenarios

### GPU FFI out-parameter results are never read from a DynLib return value

#### routes no out-parameter C symbol through a DynLib callN

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes no out-parameter C symbol through a DynLib callN
   - Expected: report equals ``
   - Expected: offenders equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes no out-parameter C symbol through a DynLib callN")
var offenders = 0
var report = ""

for path in ffi_sources():
    val maybe_source = rt_fs_read_text(path)
    if maybe_source == nil:
        continue
    val source = maybe_source

    for sym in out_param_symbols():
        for form in dyn_call_forms():
            # e.g. the historical defect: .call0("cuDeviceGetCount")
            val needle = form + "(\"" + sym + "\""
            if source.contains(needle):
                offenders = offenders + 1
                report = report + path + " -> " + needle + "; "

# An offending site means a success status is being handed back to a
# caller as if it were a count, a handle, or a device pointer.
expect(report).to_equal("")
expect(offenders).to_equal(0)
```

</details>

#### scans a non-empty corpus so a green verdict is not vacuous

- scans a non-empty corpus so a green verdict is not vacuous
   - Expected: readable > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scans a non-empty corpus so a green verdict is not vacuous")
# If every path went missing this spec would pass while checking
# nothing — the exact silent-green shape it exists to catch.
var readable = 0
for path in ffi_sources():
    if rt_fs_read_text(path) != nil:
        readable = readable + 1

expect(readable > 0).to_equal(true)
```

</details>

#### detects the historical defect shape when it is present

- detects the historical defect shape when it is present
   - Expected: pre_fix_line contains `needle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detects the historical defect shape when it is present")
# Selftest of the matcher itself: the pre-fix source line must be
# recognised by the same needle construction used above.
val pre_fix_line = "                    self._dyn_lib.call0(\"cuDeviceGetCount\")"
val needle = "call0(\"cuDeviceGetCount\""

expect(pre_fix_line.contains(needle)).to_equal(true)
```

</details>

#### keeps the CUDA dispatcher itself clean of every listed out-param symbol

- keeps the CUDA dispatcher itself clean of every listed out-param symbol
   - Expected: maybe_source != nil is true
   - Expected: source does not contain `call0("cuDeviceGetCount"`
   - Expected: source does not contain `call2("cuCtxCreate"`
   - Expected: source does not contain `call1("cuMemAlloc"`
   - Expected: source does not contain `call0("cuInit"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the CUDA dispatcher itself clean of every listed out-param symbol")
val maybe_source = rt_fs_read_text("src/lib/nogc_sync_mut/gpu/engine2d/ffi_cuda.spl")
expect(maybe_source != nil).to_equal(true)
val source = maybe_source

expect(source.contains("call0(\"cuDeviceGetCount\"")).to_equal(false)
expect(source.contains("call2(\"cuCtxCreate\"")).to_equal(false)
expect(source.contains("call1(\"cuMemAlloc\"")).to_equal(false)

# cuInit genuinely has no out param, but it DOES take a flags argument,
# so it must never be invoked through the zero-argument form.
expect(source.contains("call0(\"cuInit\"")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/ffi_out_param_via_return_value_detection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GPU FFI out-parameter results are never read from a DynLib return value.
- GPU FFI out-parameter results are never read from a DynLib return value

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1814ec8f2325ec1e5c427ede752641450eb8d1004367427d049d1aec7b7b6dab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1814ec8f2325ec1e5c427ede752641450eb8d1004367427d049d1aec7b7b6dab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1814ec8f2325ec1e5c427ede752641450eb8d1004367427d049d1aec7b7b6dab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gpu/engine2d/ffi_out_param_via_return_value_detection_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/ffi_out_param_via_return_value_detection_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=40
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gpu/engine2d/ffi_out_param_via_return_value_detection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/ffi_out_param_via_return_value_detection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/ffi_out_param_via_return_value_detection_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/gpu/engine2d/ffi_out_param_via_return_value_detection_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine2d/ffi_out_param_via_return_value_detection_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes no out-parameter C symbol through a DynLib callN' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/ffi_out_param_via_return_value_detection_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scans a non-empty corpus so a green verdict is not vacuous' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/ffi_out_param_via_return_value_detection_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects the historical defect shape when it is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
