# Test Runner Main HIR Contract

> Locks the Stage4-safe owners and daemon duration scope in both runner mirrors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Main HIR Contract

Locks the Stage4-safe owners and daemon duration scope in both runner mirrors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/test_runner_main_hir_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Locks the Stage4-safe owners and daemon duration scope in both runner mirrors.

## Scenarios

### test runner main HIR contract

#### imports time and atomic file helpers from concrete owners

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- imports time and atomic file helpers from concrete owners
   - Expected: source does not contain `use std.io.{time_now_unix_micros}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("imports time and atomic file helpers from concrete owners")
val source = rt_file_read_text("src/app/test_runner_new/test_runner_main.spl") ?? ""
expect(source).to_contain("use std.nogc_sync_mut.io.time_ops.{time_now_unix_micros}")
expect(source).to_contain("use std.nogc_sync_mut.io.file_ops.{file_atomic_write}")
expect(source.contains("use std.io.{time_now_unix_micros}")).to_equal(false)
```

</details>

#### keeps daemon duration visible to success and failure branches

- keeps daemon duration visible to success and failure branches


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps daemon duration visible to success and failure branches")
val source = rt_file_read_text("src/app/test_runner_new/test_runner_main.spl") ?? ""
val duration = source.index_of("val duration_ms = (time_now_unix_micros() - start_time) / 1000")
val branch = source.index_of("if daemon_result.status == TRESP_COMPLETED")
expect(duration).to_be_less_than(branch)
expect(source).to_contain("monitor_timeout.to_int() ?? 0")
```

</details>

#### applies the same adjacent fixes to the library runner mirror

- applies the same adjacent fixes to the library runner mirror


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("applies the same adjacent fixes to the library runner mirror")
val source = rt_file_read_text("src/lib/nogc_sync_mut/test_runner/test_runner_main.spl") ?? ""
expect(source).to_contain("use std.nogc_sync_mut.io.time_ops.{time_now_unix_micros}")
expect(source).to_contain("monitor_timeout.to_int() ?? 0")
val duration = source.index_of("val duration_ms = (time_now_unix_micros() - start_time) / 1000")
val branch = source.index_of("if daemon_result.status == TRESP_COMPLETED")
expect(duration).to_be_less_than(branch)
```

</details>

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

- Canonical SPipe generation for source `0843853edeb88143ad6ca9e414eff3d7ed5f050452a23383b3d93e3188067d97`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0843853edeb88143ad6ca9e414eff3d7ed5f050452a23383b3d93e3188067d97`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0843853edeb88143ad6ca9e414eff3d7ed5f050452a23383b3d93e3188067d97`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/test_runner_new/test_runner_main_hir_contract_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner_new/test_runner_main_hir_contract_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/app/test_runner_new/test_runner_main_hir_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner_new/test_runner_main_hir_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner_new/test_runner_main_hir_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/test_runner_new/test_runner_main_hir_contract_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports time and atomic file helpers from concrete owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_new/test_runner_main_hir_contract_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps daemon duration visible to success and failure branches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_new/test_runner_main_hir_contract_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies the same adjacent fixes to the library runner mirror' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
