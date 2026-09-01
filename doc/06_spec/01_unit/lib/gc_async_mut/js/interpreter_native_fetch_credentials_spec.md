# Interpreter Native Fetch Credentials Specification

> Tests covering JS native fetch credentials.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interpreter Native Fetch Credentials Specification

## Scenarios

### JS native fetch credentials

#### defaults an option-less fetch to same-origin credentials

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults an option-less fetch to same-origin credentials


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults an option-less fetch to same-origin credentials")
expect(_fetch_request_credentials(
    "window.fetch('/a'); 'ok'"
)).to_equal("same-origin")
```

</details>

#### propagates an explicit include credentials mode to the request

- propagates an explicit include credentials mode to the request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates an explicit include credentials mode to the request")
expect(_fetch_request_credentials(
    "window.fetch('/a', { credentials: 'include' }); 'ok'"
)).to_equal("include")
```

</details>

#### propagates an explicit omit credentials mode to the request

- propagates an explicit omit credentials mode to the request


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates an explicit omit credentials mode to the request")
expect(_fetch_request_credentials(
    "window.fetch('/a', { credentials: 'omit' }); 'ok'"
)).to_equal("omit")
```

</details>

#### normalizes credentials case and surrounding whitespace

- normalizes credentials case and surrounding whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes credentials case and surrounding whitespace")
expect(_fetch_request_credentials(
    "window.fetch('/a', { credentials: '  INCLUDE  ' }); 'ok'"
)).to_equal("include")
```

</details>

#### ignores an unrecognized credentials mode and keeps the same-origin default

- ignores an unrecognized credentials mode and keeps the same-origin default


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores an unrecognized credentials mode and keeps the same-origin default")
expect(_fetch_request_credentials(
    "window.fetch('/a', { credentials: 'bogus-mode' }); 'ok'"
)).to_equal("same-origin")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/js/interpreter_native_fetch_credentials_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JS native fetch credentials.
- JS native fetch credentials

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `ecfea35d5b75000518fdecbffc5fd1909bfa41bfc0dba2c8e9e12f1913b06c06`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ecfea35d5b75000518fdecbffc5fd1909bfa41bfc0dba2c8e9e12f1913b06c06`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ecfea35d5b75000518fdecbffc5fd1909bfa41bfc0dba2c8e9e12f1913b06c06`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/js/interpreter_native_fetch_credentials_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/js/interpreter_native_fetch_credentials_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/js/interpreter_native_fetch_credentials_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/js/interpreter_native_fetch_credentials_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/js/interpreter_native_fetch_credentials_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults an option-less fetch to same-origin credentials' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/js/interpreter_native_fetch_credentials_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates an explicit include credentials mode to the request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/js/interpreter_native_fetch_credentials_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'propagates an explicit omit credentials mode to the request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
