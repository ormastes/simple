# Module Lowering Dict Keys Source Specification

> Tests covering HIR module lowering Dict key traversal source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Lowering Dict Keys Source Specification

## Scenarios

### HIR module lowering Dict key traversal source

#### uses typed Dict runtime views instead of ambiguous Map dispatch

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses typed Dict runtime views instead of ambiguous Map dispatch
   - Expected: source does not contain `.keys()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses typed Dict runtime views instead of ambiguous Map dispatch")
val source = rt_file_read_text("src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl") ?? ""

# NOTE: braces escaped (\{ \}) -- an un-escaped `{rt_dict_keys}` here is
# resolved by THIS spec's own lexer as string interpolation and dies with
# `semantic: variable rt_dict_keys not found`, making the RED measure the
# spec itself instead of the product source.
expect(source).to_contain("use std.alloc.sffi.\{rt_dict_keys\}")
expect(source).to_contain("val cls_keys: [text] = rt_dict_keys(module_classes)")
expect(source).to_contain("val fn_keys: [text] = rt_dict_keys(module_functions)")
expect(source).to_contain("val lowered_impl_function_keys: [SymbolId] = rt_dict_keys(self.lowered_impl_functions)")
expect(source).to_contain("me register_glob_imported_symbols(imported_mod: Module")
expect(source).to_contain("var keys: [text] = rt_dict_keys(imported_mod.classes)")
expect(source.contains(".keys()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HIR module lowering Dict key traversal source.
- HIR module lowering Dict key traversal source

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bb3f0849d066d805a8e1519b98829d157cfc7891b81e37cd477e089bec7a3ade`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bb3f0849d066d805a8e1519b98829d157cfc7891b81e37cd477e089bec7a3ade`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bb3f0849d066d805a8e1519b98829d157cfc7891b81e37cd477e089bec7a3ade`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/hir/module_lowering_dict_keys_source_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses typed Dict runtime views instead of ambiguous Map dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
