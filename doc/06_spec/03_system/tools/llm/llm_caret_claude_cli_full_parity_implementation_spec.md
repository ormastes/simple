# LLM Caret Claude CLI Full-Parity Implementation Gate

> This release gate binds the frozen Claude source inventory to implemented Simple target files. It is intentionally strict: a planned row is not an implemented feature, and a class row is not accepted unless its target exists.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Claude CLI Full-Parity Implementation Gate

This release gate binds the frozen Claude source inventory to implemented Simple target files. It is intentionally strict: a planned row is not an implemented feature, and a class row is not accepted unless its target exists.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Red gate until `src/app/llm_caret/claude_full/**` is implemented |
| Requirements | doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md |
| Plan | doc/03_plan/sys_test/llm_caret_claude_cli_full_parity.md |
| Design | doc/05_design/llm_caret_claude_cli_full_parity.md |
| Research | doc/01_research/local/llm_caret_claude_cli_harden.md |
| Source | `test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This release gate binds the frozen Claude source inventory to implemented
Simple target files. It is intentionally strict: a planned row is not an
implemented feature, and a class row is not accepted unless its target exists.

## Syntax

```bash
sh scripts/check/check-llm-caret-full-parity-plan.shs
sh scripts/check/check-llm-caret-full-parity-implementation.shs
bin/simple test test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl --mode=interpreter
```

## Operator Flow

1. Confirm the full-parity matrices still match the Claude source inventory.
2. Run the strict implementation checker.
3. Require every mapped target file to exist.
4. Require every mapped target file to meet the full target LOC gate.
5. Require every mapped target file to meet the 80 percent size floor.
6. Require every mapped class row to point at an implemented target file.

This spec intentionally fails while the implementation is only a plan. The
older traceability gate proves an 80 percent migration map for the compact
caret; this gate proves the requested full Claude CLI parity implementation.

## Inventory Contract

The plan checker requires:

- 1,902 Claude source-file rows;
- 599 feature rows;
- 14,119 symbol rows;
- the checked-out Claude evidence tree;
- exact agreement between the evidence tree and frozen matrices.

The implementation checker requires:

- every mapped Simple target file to exist;
- every target to meet its required LOC;
- every target to meet the 80 percent source-size floor;
- every Claude class row to resolve to an implemented target;
- a final explicit PASS marker.

## Scenario Details

### Artifact Presence

The first scenario checks both matrices and both checkers before invoking any
expensive inventory work. Missing evidence is reported as failure rather than
silently skipped.

### Frozen Plan Inventory

The second scenario runs the plan checker exactly once. It verifies file,
feature, and symbol row counts together with the plan PASS marker.

### Implementation Parity

The third scenario runs the implementation checker exactly once. The same
captured output is used for file, LOC, and class assertions so the expensive
tree scan is not duplicated.

## Failure Interpretation

`target_files_missing` means mapped Simple implementation files do not exist.

`target_loc_lt_80pct_source` means existing targets are still below the source
size floor.

`class_target_files_missing` means one or more mapped Claude classes lack an
implemented Simple target.

A missing `STATUS: PASS` line means the checker rejected the current tree even
when individual counters look plausible.

## Safety

The checkers are offline. They inspect tracked matrices, the local Claude
evidence fixture, and Simple source files. They do not authenticate, invoke the
Claude CLI, or make paid API calls.

## Evidence Boundary

Passing this gate proves inventory and size parity. It does not by itself prove
that each behavior is correct. Focused unit, integration, CLI, hidden-feature,
and TUI system specs provide behavioral evidence.

## Completion Rule

The gate remains red until all counters meet their exact targets and the final
PASS marker is present. Partial percentage improvement is progress but is not
release acceptance.

## Scenarios

### LLM caret Claude CLI full-parity implementation

#### should keep the plan matrices and checkers available

- should keep the plan matrices and checkers available
- Confirm the generated matrices and checker scripts are present


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the plan matrices and checkers available")
step("Confirm the generated matrices and checker scripts are present")
expect(file_exists(FILE_MATRIX)).to_be(true)
expect(file_exists(SYMBOL_MATRIX)).to_be(true)
expect(file_exists(PLAN_CHECK)).to_be(true)
expect(file_exists(IMPL_CHECK)).to_be(true)
```

</details>

#### should require the pinned Claude source tree instead of historical rows alone

- should require the pinned Claude source tree instead of historical rows alone
- Confirm the provenance-pinned Claude source inventory is present
   - Expected: dir_exists(UPSTREAM_SRC) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require the pinned Claude source tree instead of historical rows alone")
step("Confirm the provenance-pinned Claude source inventory is present")
expect(dir_exists(UPSTREAM_SRC)).to_equal(true)
```

</details>

#### should keep the full-parity plan inventory matched to Claude source

- should keep the full-parity plan inventory matched to Claude source
- Run the plan checker against the Claude source tree and matrices
   - Expected: result.1 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the full-parity plan inventory matched to Claude source")
step("Run the plan checker against the Claude source tree and matrices")
val result = run_check(PLAN_CHECK)
val output = result.0

expect(result.1).to_equal(0)
expect(output).to_contain("claude_source_files=1902")
expect(output).to_contain("full_parity_file_rows=1902")
expect(output).to_contain("full_parity_feature_rows=599")
expect(output).to_contain("full_parity_symbol_rows=14119")
expect(output).to_contain("STATUS: PASS llm-caret-full-parity-plan")
```

</details>

#### should prove mapped files and Claude classes reach implementation parity

- should prove mapped files and Claude classes reach implementation parity
- Run the strict implementation checker once for file, size, and class parity
   - Expected: result.1 equals `0`
- Check class rows resolve to implemented Simple target files


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should prove mapped files and Claude classes reach implementation parity")
step("Run the strict implementation checker once for file, size, and class parity")
val result = run_check(IMPL_CHECK)
val output = result.0

expect(result.1).to_equal(0)
expect(output).to_contain("file_rows=1902")
expect(output).to_contain("target_files_missing=0")
expect(output).to_contain("target_loc_lt_80pct_source=0")
expect(output).to_contain("target_loc_ge_required=1902")
step("Check class rows resolve to implemented Simple target files")
expect(output).to_contain("class_rows=124")
expect(output).to_contain("class_target_files_missing=0")
expect(output).to_contain("STATUS: PASS llm-caret-full-parity-implementation")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_claude_cli_full_parity.md`
- **Design:** `doc/05_design/llm_caret_claude_cli_full_parity.md`
- **Research:** `doc/01_research/local/llm_caret_claude_cli_harden.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-FULL-001`
- `REQ-LLM-CARET-FULL-002`
- `REQ-LLM-CARET-FULL-003`
- `REQ-LLM-CARET-FULL-004`
- `REQ-LLM-CARET-FULL-005`
- `REQ-LLM-CARET-FULL-006`
- `REQ-LLM-CARET-FULL-007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5f97c3677351e781c6599e458af46ae36aeddc37d03e9b8ce0c7d4e7b6c87fe2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f97c3677351e781c6599e458af46ae36aeddc37d03e9b8ce0c7d4e7b6c87fe2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f97c3677351e781c6599e458af46ae36aeddc37d03e9b8ce0c7d4e7b6c87fe2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl
mirror: doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl:144:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the plan matrices and checkers available' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep the plan matrices and checkers available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl:153:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require the pinned Claude source tree instead of historical rows alone' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require the pinned Claude source tree instead of historical rows alone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl:159:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the full-parity plan inventory matched to Claude source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep the full-parity plan inventory matched to Claude source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl:173:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prove mapped files and Claude classes reach implementation parity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
