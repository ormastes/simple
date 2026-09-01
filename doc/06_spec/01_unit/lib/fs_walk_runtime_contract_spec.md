# Fs Walk Runtime Contract Specification

> Tests covering filesystem walk runtime contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fs Walk Runtime Contract Specification

## Scenarios

### filesystem walk runtime contract

#### maps runtime paths instead of binding an unrelated walk_dir symbol

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps runtime paths instead of binding an unrelated walk_dir symbol
   - Expected: source does not contain `extern fn walk_dir`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps runtime paths instead of binding an unrelated walk_dir symbol")
val sync_source = rt_file_read_text("src/lib/nogc_sync_mut/fs.spl") ?? ""
val async_source = rt_file_read_text("src/lib/nogc_async_mut/fs.spl") ?? ""

for source in [sync_source, async_source]:
    expect(source).to_contain("extern fn rt_dir_walk(root: text) -> [text]")
    expect(source).to_contain("entries.push(DirEntry(")
    expect(source.contains("extern fn walk_dir")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/fs_walk_runtime_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering filesystem walk runtime contract.
- filesystem walk runtime contract

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3b6f6fc04ec5188d86911f26ca27562d93948749dedfc27ec1864119a8b6fb2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b6f6fc04ec5188d86911f26ca27562d93948749dedfc27ec1864119a8b6fb2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b6f6fc04ec5188d86911f26ca27562d93948749dedfc27ec1864119a8b6fb2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/fs_walk_runtime_contract_spec.spl
mirror: doc/06_spec/01_unit/lib/fs_walk_runtime_contract_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/lib/fs_walk_runtime_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/fs_walk_runtime_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/fs_walk_runtime_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/fs_walk_runtime_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/fs_walk_runtime_contract_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps runtime paths instead of binding an unrelated walk_dir symbol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
