# LLM Caret Claude CLI Full-Parity Implementation Gate

> This release gate binds the frozen Claude source inventory to implemented Simple target files. It is intentionally strict: a planned row is not an implemented feature, and a class row is not accepted unless its target exists.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

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
| Updated | 2026-07-24 |
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

- Confirm the generated matrices and checker scripts are present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Confirm the generated matrices and checker scripts are present")
expect(file_exists(FILE_MATRIX)).to_be(true)
expect(file_exists(SYMBOL_MATRIX)).to_be(true)
expect(file_exists(PLAN_CHECK)).to_be(true)
expect(file_exists(IMPL_CHECK)).to_be(true)
```

</details>

#### should keep the full-parity plan inventory matched to Claude source

- Run the plan checker against the Claude source tree and matrices


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the plan checker against the Claude source tree and matrices")
val output = run_check(PLAN_CHECK)

expect(output).to_contain("claude_source_files=1902")
expect(output).to_contain("full_parity_file_rows=1902")
expect(output).to_contain("full_parity_feature_rows=599")
expect(output).to_contain("full_parity_symbol_rows=14119")
expect(output).to_contain("STATUS: PASS llm-caret-full-parity-plan")
```

</details>

#### should prove mapped files and Claude classes reach implementation parity

- Run the strict implementation checker once for file, size, and class parity
- Check class rows resolve to implemented Simple target files


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the strict implementation checker once for file, size, and class parity")
val output = run_check(IMPL_CHECK)

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
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_caret_claude_cli_full_parity.md`
- **Plan:** `doc/03_plan/sys_test/llm_caret_claude_cli_full_parity.md`
- **Design:** `doc/05_design/llm_caret_claude_cli_full_parity.md`
- **Research:** `doc/01_research/local/llm_caret_claude_cli_harden.md`


</details>
