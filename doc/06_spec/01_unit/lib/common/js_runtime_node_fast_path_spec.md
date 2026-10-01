# Js Runtime Node Fast Path Specification

> Tests covering JsRuntime Node host fast paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Runtime Node Fast Path Specification

## Scenarios

### JsRuntime Node host fast paths

#### fast paths process cwd probes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fast paths process cwd probes
   - Expected: _runtime_eval_text("process.cwd()") equals `/`
   - Expected: _runtime_eval_text("require('process').cwd()") equals `/`
   - Expected: _runtime_eval_text("require(\"process\").cwd()") equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fast paths process cwd probes")
expect(_runtime_eval_text("process.cwd()")).to_equal("/")
expect(_runtime_eval_text("require('process').cwd()")).to_equal("/")
expect(_runtime_eval_text("require(\"process\").cwd()")).to_equal("/")
```

</details>

#### fast paths process argv probes

- fast paths process argv probes
   - Expected: _runtime_eval_text("process.argv.length") equals `2`
   - Expected: _runtime_eval_text("process.argv[0]") equals `simple`
   - Expected: _runtime_eval_text("require('process').argv.length") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fast paths process argv probes")
expect(_runtime_eval_text("process.argv.length")).to_equal("2")
expect(_runtime_eval_text("process.argv[0]")).to_equal("simple")
expect(_runtime_eval_text("require('process').argv.length")).to_equal("2")
```

</details>

#### fast paths Buffer byteLength probes

- fast paths Buffer byteLength probes
   - Expected: _runtime_eval_text("require('buffer').Buffer.byteLength('hello', 'utf8')") equals `5`
   - Expected: _runtime_eval_text("require(\"buffer\").Buffer.byteLength(\"hello\", \"utf8\")") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fast paths Buffer byteLength probes")
expect(_runtime_eval_text("require('buffer').Buffer.byteLength('hello', 'utf8')")).to_equal("5")
expect(_runtime_eval_text("require(\"buffer\").Buffer.byteLength(\"hello\", \"utf8\")")).to_equal("5")
```

</details>

#### fast paths Buffer.from toString probes

- fast paths Buffer.from toString probes
   - Expected: _runtime_eval_text("require('buffer').Buffer.from('68656c6c6f', 'hex').toString('utf8')") equals `hello`
   - Expected: _runtime_eval_text("require(\"buffer\").Buffer.from(\"68656c6c6f\", \"hex\").toString(\"utf8\")") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fast paths Buffer.from toString probes")
expect(_runtime_eval_text("require('buffer').Buffer.from('68656c6c6f', 'hex').toString('utf8')")).to_equal("hello")
expect(_runtime_eval_text("require(\"buffer\").Buffer.from(\"68656c6c6f\", \"hex\").toString(\"utf8\")")).to_equal("hello")
```

</details>

#### fast paths deterministic os tmpdir probes

- fast paths deterministic os tmpdir probes
   - Expected: _runtime_eval_text("require('os').tmpdir()") equals `/tmp`
   - Expected: _runtime_eval_text("require('node:os').tmpdir()") equals `/tmp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fast paths deterministic os tmpdir probes")
expect(_runtime_eval_text("require('os').tmpdir()")).to_equal("/tmp")
expect(_runtime_eval_text("require('node:os').tmpdir()")).to_equal("/tmp")
```

</details>

#### fast paths deterministic os endianness probes

- fast paths deterministic os endianness probes
   - Expected: _runtime_eval_text("require('os').endianness()") equals `LE`
   - Expected: _runtime_eval_text("require('node:os').endianness()") equals `LE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fast paths deterministic os endianness probes")
expect(_runtime_eval_text("require('os').endianness()")).to_equal("LE")
expect(_runtime_eval_text("require('node:os').endianness()")).to_equal("LE")
```

</details>

#### fast paths deterministic os EOL probes

- fast paths deterministic os EOL probes
   - Expected: _runtime_eval_text("require('os').EOL") equals `\n`
   - Expected: _runtime_eval_text("require('node:os').EOL") equals `\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fast paths deterministic os EOL probes")
expect(_runtime_eval_text("require('os').EOL")).to_equal("\n")
expect(_runtime_eval_text("require('node:os').EOL")).to_equal("\n")
```

</details>

#### fast paths os and node:os aliases consistently

- fast paths os and node:os aliases consistently
   - Expected: _runtime_eval_text("require('os').type()") equals `Linux`
   - Expected: _runtime_eval_text("require('node:os').release()") equals `0.0.0-simple`
   - Expected: _runtime_eval_text("require('node:os').homedir()") equals `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fast paths os and node:os aliases consistently")
expect(_runtime_eval_text("require('os').type()")).to_equal("Linux")
expect(_runtime_eval_text("require('node:os').release()")).to_equal("0.0.0-simple")
expect(_runtime_eval_text("require('node:os').homedir()")).to_equal("/")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/js_runtime_node_fast_path_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JsRuntime Node host fast paths.
- JsRuntime Node host fast paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `845cd3f9226f4807be1973520806fe9cfc737a581058a7cd0d245fe492c0aed6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `845cd3f9226f4807be1973520806fe9cfc737a581058a7cd0d245fe492c0aed6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `845cd3f9226f4807be1973520806fe9cfc737a581058a7cd0d245fe492c0aed6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/js_runtime_node_fast_path_spec.spl
mirror: doc/06_spec/01_unit/lib/common/js_runtime_node_fast_path_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/js_runtime_node_fast_path_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/js_runtime_node_fast_path_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/js_runtime_node_fast_path_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fast paths process cwd probes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/js_runtime_node_fast_path_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fast paths process argv probes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/js_runtime_node_fast_path_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fast paths Buffer byteLength probes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
