# Method Self Context Save Restore Specification

> Tests covering method self-context save/restore across all lowering paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Method Self Context Save Restore Specification

## Scenarios

### method self-context save/restore across all lowering paths

#### declaration_lowering saves and restores current_method_self_symbol_id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- declaration_lowering saves and restores current_method_self_symbol_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declaration_lowering saves and restores current_method_self_symbol_id")
val source = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl") ?? ""
expect(source).to_contain("self.current_method_self_symbol_id = symbol.id")
expect(source).to_contain("self.current_method_self_symbol_id = previous_self_symbol_id")
```

</details>

#### trait_impl_lowering saves and restores current_method_self_symbol_id

- trait_impl_lowering saves and restores current_method_self_symbol_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trait_impl_lowering saves and restores current_method_self_symbol_id")
val source = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/_Items/trait_impl_lowering.spl") ?? ""
expect(source).to_contain("self.current_method_self_symbol_id = match type_.kind:")
expect(source).to_contain("self.current_method_self_symbol_id = previous_self_symbol_id")
```

</details>

#### module_lowering (flat-AST impl path) saves and restores current_method_self_symbol_id

- module_lowering (flat-AST impl path) saves and restores current_method_self_symbol_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("module_lowering (flat-AST impl path) saves and restores current_method_self_symbol_id")
val source = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl") ?? ""
expect(source).to_contain("self.current_method_self_symbol_id = impl_owner_symbol.id")
expect(source).to_contain("self.current_method_self_symbol_id = previous_impl_self_symbol_id")
```

</details>

#### the field itself still exists and initialises to -1

- the field itself still exists and initialises to -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the field itself still exists and initialises to -1")
val source = rt_file_read_text(
    "src/compiler/20.hir/hir_lowering/types.spl") ?? ""
expect(source).to_contain("current_method_self_symbol_id: i64")
expect(source).to_contain("current_method_self_symbol_id: -1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/hir/method_self_context_save_restore_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering method self-context save/restore across all lowering paths.
- method self-context save/restore across all lowering paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `ee2de6ce8f3f2561769120df0bb53178937be167aac4dd9fb8c3f8254805db63`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee2de6ce8f3f2561769120df0bb53178937be167aac4dd9fb8c3f8254805db63`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee2de6ce8f3f2561769120df0bb53178937be167aac4dd9fb8c3f8254805db63`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/hir/method_self_context_save_restore_spec.spl
mirror: doc/06_spec/unit/compiler/hir/method_self_context_save_restore_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/hir/method_self_context_save_restore_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/hir/method_self_context_save_restore_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/hir/method_self_context_save_restore_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declaration_lowering saves and restores current_method_self_symbol_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/method_self_context_save_restore_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trait_impl_lowering saves and restores current_method_self_symbol_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/hir/method_self_context_save_restore_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'module_lowering (flat-AST impl path) saves and restores current_method_self_symbol_id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
