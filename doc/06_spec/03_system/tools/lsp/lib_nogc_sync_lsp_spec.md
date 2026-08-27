# Lib Nogc Sync Lsp Specification

> Tests covering LSP System: lib/nogc_sync_mut.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lib Nogc Sync Lsp Specification

## Scenarios

### LSP System: lib/nogc_sync_mut

<details>
<summary>Advanced: hover: no crashes</summary>

#### hover: no crashes _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hover: no crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hover: no crashes")
if _can_run:
    val crashes = batch_lsp("hover", files)
    report_crashes("hover", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: definition: no crashes</summary>

#### definition: no crashes _(slow)_

- definition: no crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("definition: no crashes")
if _can_run:
    val crashes = batch_lsp("definition", files)
    report_crashes("definition", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: references: no crashes</summary>

#### references: no crashes _(slow)_

- references: no crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("references: no crashes")
if _can_run:
    val crashes = batch_lsp("references", files)
    report_crashes("references", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: completions: no crashes</summary>

#### completions: no crashes _(slow)_

- completions: no crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("completions: no crashes")
if _can_run:
    val crashes = batch_lsp("completions", files)
    report_crashes("completions", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: semantic-tokens: no crashes</summary>

#### semantic-tokens: no crashes _(slow)_

- semantic-tokens: no crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("semantic-tokens: no crashes")
if _can_run:
    val crashes = batch_lsp_no_pos("semantic-tokens", files)
    report_crashes("semantic-tokens", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: folding-range: no crashes</summary>

#### folding-range: no crashes _(slow)_

- folding-range: no crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("folding-range: no crashes")
if _can_run:
    val crashes = batch_lsp_no_pos("folding-range", files)
    report_crashes("folding-range", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: document-highlight: no crashes</summary>

#### document-highlight: no crashes _(slow)_

- document-highlight: no crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("document-highlight: no crashes")
if _can_run:
    val crashes = batch_lsp("document-highlight", files)
    report_crashes("document-highlight", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

<details>
<summary>Advanced: type-definition: no crashes</summary>

#### type-definition: no crashes _(slow)_

- type-definition: no crashes
   - Expected: crashes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("type-definition: no crashes")
if _can_run:
    val crashes = batch_lsp("type-definition", files)
    report_crashes("type-definition", crashes)
    expect(crashes.len()).to_equal(0)
else:
    print "SKIP: Simple runtime not available"
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | LSP |
| Status | Active |
| Source | `test/03_system/tools/lsp/lib_nogc_sync_lsp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LSP System: lib/nogc_sync_mut.
- LSP System: lib/nogc_sync_mut

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
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

- Canonical SPipe generation for source `f7bf09ee458b848e36cf0d722dc2f3e6c2909236cae8d75902017c66f2df2e9d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7bf09ee458b848e36cf0d722dc2f3e6c2909236cae8d75902017c66f2df2e9d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7bf09ee458b848e36cf0d722dc2f3e6c2909236cae8d75902017c66f2df2e9d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/lsp/lib_nogc_sync_lsp_spec.spl
mirror: doc/06_spec/03_system/tools/lsp/lib_nogc_sync_lsp_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/lsp/lib_nogc_sync_lsp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/lsp/lib_nogc_sync_lsp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/lsp/lib_nogc_sync_lsp_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/lsp/lib_nogc_sync_lsp_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hover: no crashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/lsp/lib_nogc_sync_lsp_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'definition: no crashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/lsp/lib_nogc_sync_lsp_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'references: no crashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
