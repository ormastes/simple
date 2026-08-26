# Leak Check Owner Imports Contract

> The Stage4 closure must resolve leak-check runtime types and driver calls from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Leak Check Owner Imports Contract

The Stage4 closure must resolve leak-check runtime types and driver calls from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The Stage4 closure must resolve leak-check runtime types and driver calls from
their concrete owner modules rather than through multi-hop facades.

## Scenarios

### leak check owner imports

#### imports the interpreter call and result type from concrete owners

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- imports the interpreter call and result type from concrete owners
   - Expected: source does not contain `use compiler.driver.\{interpret_file, CompileResult\}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("imports the interpreter call and result type from concrete owners")
val source = rt_file_read_text("src/compiler/tools/leak_check/main.spl") ?? ""
expect(source).to_contain("use compiler.driver.driver_public_interpret_bridge.\{interpret_file\}")
expect(source).to_contain("use compiler.common.driver_core_types.\{CompileResult\}")
expect(source.contains("use compiler.driver.\{interpret_file, CompileResult\}")).to_equal(false)
```

</details>

#### imports MemLeakEntry directly while retaining adjacent tracker operations

- imports MemLeakEntry directly while retaining adjacent tracker operations
   - Expected: source does not contain `parse_leak_dump, MemLeakEntry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("imports MemLeakEntry directly while retaining adjacent tracker operations")
val source = rt_file_read_text("src/compiler/tools/leak_check/main.spl") ?? ""
expect(source).to_contain("use std.mem_tracker.types.\{MemLeakEntry\}")
expect(source).to_contain("mem_enable, mem_disable, mem_snapshot, mem_dump_leaks, parse_leak_dump")
expect(source.contains("parse_leak_dump, MemLeakEntry")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `6dc3f8c6a059941787ab895faab6c02e7c74e6dff59915199f8f8f0dee2e4db3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6dc3f8c6a059941787ab895faab6c02e7c74e6dff59915199f8f8f0dee2e4db3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6dc3f8c6a059941787ab895faab6c02e7c74e6dff59915199f8f8f0dee2e4db3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/leak_check_owner_imports_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/leak_check_owner_imports_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/leak_check_owner_imports_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports the interpreter call and result type from concrete owners' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/leak_check_owner_imports_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports MemLeakEntry directly while retaining adjacent tracker operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
