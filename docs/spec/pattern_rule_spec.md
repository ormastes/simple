# PatternRulePass Specification

Validates the data-driven PatternRulePass which loads `.opt.json` rule files, matches MIR instruction sequences against named patterns, and applies rewrites. The AC-7 schema extends `simple.opt.mir.v1` with an optional `rules: [PatternRule]` array.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #web-server-optimizer-complete |
| Category | Compiler / MIR Optimization — Rule Engine |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/unit/compiler/mir_opt/pattern_rule_spec.spl` |
| Updated | 2026-05-25 |
| Generator | `simple spipe-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Validates the data-driven PatternRulePass which loads `.opt.json` rule
files, matches MIR instruction sequences against named patterns, and
applies rewrites. The AC-7 schema extends `simple.opt.mir.v1` with an
optional `rules: [PatternRule]` array.

## Behavior

- Rule file with valid schema is loaded without error
- Pattern matching finds the expected instruction sequence
- Rewrite replaces matched sequence with the rewritten form
- Rule with invalid pattern syntax is rejected at load time
- Applied rule reports its cost_delta

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 2 |
| Logs | 5 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/compiler/mir_opt/pattern_rule/result.json` |
| `summary.txt` | Text artifact | `build/test-artifacts/compiler/mir_opt/pattern_rule/summary.txt` |

### Logs

| Item | Kind | Path |
|------|------|------|
| `combined.log` | Log file | `build/test-artifacts/compiler/mir_opt/pattern_rule/combined.log` |
| `output.log` | Log file | `build/test-artifacts/compiler/mir_opt/pattern_rule/output.log` |
| `run.log` | Log file | `build/test-artifacts/compiler/mir_opt/pattern_rule/run.log` |
| `stderr.log` | Log file | `build/test-artifacts/compiler/mir_opt/pattern_rule/stderr.log` |
| `stdout.log` | Log file | `build/test-artifacts/compiler/mir_opt/pattern_rule/stdout.log` |

## Scenarios

- loads .opt.json rule file and validates schema
- rejects rule with invalid pattern syntax
- rejects file with unknown schema version
- matches MIR pattern against instruction sequence
- returns -1 when pattern is not present in sequence
- applies rewrite to matched instructions
- reports cost delta for applied rule
