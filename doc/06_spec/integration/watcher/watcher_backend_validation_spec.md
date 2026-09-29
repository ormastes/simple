# Watcher Backend Validation Specification

> Tests covering Backend Validation, matching backends, mismatching backends, opt level mismatch, release flag mismatch, missing module, hash stability.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Watcher Backend Validation Specification

## Scenarios

### Backend Validation

### matching backends

<details>
<summary>Advanced: LLVM compiled, LLVM loaded</summary>

#### LLVM compiled, LLVM loaded _(slow)_

- LLVM compiled, LLVM loaded
   - Expected: result equals `ok`
   - Expected: ldr_warnings_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("LLVM compiled, LLVM loaded")
ldr_reset()
val hash = mock_compute("llvm", 2, true)
ldr_store("main.smf", hash)
val result = ldr_load_validated("main.smf", hash)
expect(result).to_equal("ok")
expect(ldr_warnings_len()).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: Cranelift compiled, Cranelift loaded</summary>

#### Cranelift compiled, Cranelift loaded _(slow)_

- Cranelift compiled, Cranelift loaded
   - Expected: result equals `ok`
   - Expected: ldr_warnings_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Cranelift compiled, Cranelift loaded")
ldr_reset()
val hash = mock_compute("cranelift", 1, false)
ldr_store("main.smf", hash)
val result = ldr_load_validated("main.smf", hash)
expect(result).to_equal("ok")
expect(ldr_warnings_len()).to_equal(0)
```

</details>


</details>

### mismatching backends

<details>
<summary>Advanced: LLVM compiled, Cranelift loaded warns</summary>

#### LLVM compiled, Cranelift loaded warns _(slow)_

- LLVM compiled, Cranelift loaded warns
   - Expected: result equals `mismatch`
   - Expected: ldr_warnings_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("LLVM compiled, Cranelift loaded warns")
ldr_reset()
val llvm_hash = mock_compute("llvm", 2, true)
val crank_hash = mock_compute("cranelift", 2, true)
ldr_store("main.smf", llvm_hash)
val result = ldr_load_validated("main.smf", crank_hash)
expect(result).to_equal("mismatch")
expect(ldr_warnings_len()).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: Cranelift compiled, LLVM loaded warns</summary>

#### Cranelift compiled, LLVM loaded warns _(slow)_

- Cranelift compiled, LLVM loaded warns
   - Expected: result equals `mismatch`
   - Expected: ldr_warnings_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("Cranelift compiled, LLVM loaded warns")
ldr_reset()
val crank_hash = mock_compute("cranelift", 1, false)
val llvm_hash = mock_compute("llvm", 1, false)
ldr_store("main.smf", crank_hash)
val result = ldr_load_validated("main.smf", llvm_hash)
expect(result).to_equal("mismatch")
expect(ldr_warnings_len()).to_equal(1)
```

</details>


</details>

### opt level mismatch

<details>
<summary>Advanced: different opt levels detected</summary>

#### different opt levels detected _(slow)_

- different opt levels detected
   - Expected: result equals `mismatch`
   - Expected: ldr_warnings_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("different opt levels detected")
ldr_reset()
val hash_o0 = mock_compute("llvm", 0, false)
val hash_o3 = mock_compute("llvm", 3, false)
ldr_store("main.smf", hash_o0)
val result = ldr_load_validated("main.smf", hash_o3)
expect(result).to_equal("mismatch")
expect(ldr_warnings_len()).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: same opt level is ok</summary>

#### same opt level is ok _(slow)_

- same opt level is ok
   - Expected: result equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("same opt level is ok")
ldr_reset()
val hash = mock_compute("llvm", 2, false)
ldr_store("main.smf", hash)
val result = ldr_load_validated("main.smf", hash)
expect(result).to_equal("ok")
```

</details>


</details>

### release flag mismatch

<details>
<summary>Advanced: debug vs release detected</summary>

#### debug vs release detected _(slow)_

- debug vs release detected
   - Expected: result equals `mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("debug vs release detected")
ldr_reset()
val debug_hash = mock_compute("llvm", 2, false)
val release_hash = mock_compute("llvm", 2, true)
ldr_store("main.smf", debug_hash)
val result = ldr_load_validated("main.smf", release_hash)
expect(result).to_equal("mismatch")
```

</details>


</details>

### missing module

<details>
<summary>Advanced: reports missing for unloaded module</summary>

#### reports missing for unloaded module _(slow)_

- reports missing for unloaded module
   - Expected: result equals `missing`
   - Expected: ldr_warnings_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports missing for unloaded module")
ldr_reset()
val hash = mock_compute("llvm", 2, true)
val result = ldr_load_validated("nonexistent.smf", hash)
expect(result).to_equal("missing")
expect(ldr_warnings_len()).to_equal(0)
```

</details>


</details>

### hash stability

<details>
<summary>Advanced: same options always produce same hash</summary>

#### same options always produce same hash _(slow)_

- same options always produce same hash
   - Expected: h1 equals `h2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("same options always produce same hash")
val h1 = mock_compute("cranelift", 2, true)
val h2 = mock_compute("cranelift", 2, true)
expect(h1).to_equal(h2)
```

</details>


</details>

<details>
<summary>Advanced: different options produce different hashes</summary>

#### different options produce different hashes _(slow)_

- different options produce different hashes
   - Expected: h1 != h2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("different options produce different hashes")
val h1 = mock_compute("llvm", 2, true)
val h2 = mock_compute("cranelift", 2, true)
expect(h1 != h2).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Active |
| Source | `test/integration/watcher/watcher_backend_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Backend Validation, matching backends, mismatching backends, opt level mismatch, release flag mismatch, missing module, hash stability.
- Backend Validation
- matching backends
- mismatching backends
- opt level mismatch
- release flag mismatch
- missing module
- hash stability

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1a21d8194666d7f8d1d20a00abcc02cbac16cde1190400c3c0dcc283588d0de1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a21d8194666d7f8d1d20a00abcc02cbac16cde1190400c3c0dcc283588d0de1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a21d8194666d7f8d1d20a00abcc02cbac16cde1190400c3c0dcc283588d0de1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/watcher/watcher_backend_validation_spec.spl
mirror: doc/06_spec/integration/watcher/watcher_backend_validation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/watcher/watcher_backend_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/watcher/watcher_backend_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/watcher/watcher_backend_validation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/watcher/watcher_backend_validation_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LLVM compiled, LLVM loaded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/watcher/watcher_backend_validation_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Cranelift compiled, Cranelift loaded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/watcher/watcher_backend_validation_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LLVM compiled, Cranelift loaded warns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
