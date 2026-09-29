# Custom Editor Contribution Specification

> Tests covering extension manifest contributes_custom_editors binds into a resolvable registry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Custom Editor Contribution Specification

## Scenarios

### extension manifest contributes_custom_editors binds into a resolvable registry

#### is unresolved before activation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is unresolved before activation
   - Expected: host.custom_editor_registered("demo.kind") is false
   - Expected: host.resolve_custom_editor("demo.kind").extension_name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is unresolved before activation")
val host = ExtensionHost.new()
host.register_manifest(ce_demo_manifest(), "<test>")
expect(host.custom_editor_registered("demo.kind")).to_equal(false)
expect(host.resolve_custom_editor("demo.kind").extension_name).to_equal("")
```

</details>

#### binds the contributed custom editor on activate, resolvable by document_kind

- binds the contributed custom editor on activate, resolvable by document_kind
   - Expected: host.activate("ce-demo") is true
   - Expected: host.custom_editor_registered("demo.kind") is true
   - Expected: resolved.extension_name equals `ce-demo`
   - Expected: resolved.editor.id equals `ce.demo.editor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("binds the contributed custom editor on activate, resolvable by document_kind")
val host = ExtensionHost.new()
host.register_manifest(ce_demo_manifest(), "<test>")
expect(host.activate("ce-demo")).to_equal(true)
expect(host.custom_editor_registered("demo.kind")).to_equal(true)
val resolved = host.resolve_custom_editor("demo.kind")
expect(resolved.extension_name).to_equal("ce-demo")
expect(resolved.editor.id).to_equal("ce.demo.editor")
```

</details>

#### reverses the binding on deactivate

- reverses the binding on deactivate
   - Expected: host.custom_editor_registered("demo.kind") is true
   - Expected: host.deactivate("ce-demo") is true
   - Expected: host.custom_editor_registered("demo.kind") is false
   - Expected: host.resolve_custom_editor("demo.kind").extension_name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reverses the binding on deactivate")
val host = ExtensionHost.new()
host.register_manifest(ce_demo_manifest(), "<test>")
host.activate("ce-demo")
expect(host.custom_editor_registered("demo.kind")).to_equal(true)
expect(host.deactivate("ce-demo")).to_equal(true)
expect(host.custom_editor_registered("demo.kind")).to_equal(false)
expect(host.resolve_custom_editor("demo.kind").extension_name).to_equal("")
```

</details>

#### re-binds on re-activate after deactivate

- re-binds on re-activate after deactivate
   - Expected: host.custom_editor_registered("demo.kind") is false
   - Expected: host.activate("ce-demo") is true
   - Expected: host.resolve_custom_editor("demo.kind").editor.id equals `ce.demo.editor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("re-binds on re-activate after deactivate")
val host = ExtensionHost.new()
host.register_manifest(ce_demo_manifest(), "<test>")
host.activate("ce-demo")
host.deactivate("ce-demo")
expect(host.custom_editor_registered("demo.kind")).to_equal(false)
expect(host.activate("ce-demo")).to_equal(true)
expect(host.resolve_custom_editor("demo.kind").editor.id).to_equal("ce.demo.editor")
```

</details>

#### deactivating one extension leaves a sibling extension's custom editor bound

- deactivating one extension leaves a sibling extension's custom editor bound
   - Expected: host.resolve_custom_editor("demo.kind").extension_name equals `ce-demo`
   - Expected: host.resolve_custom_editor("sibling.kind").extension_name equals `ce-sibling-demo`
   - Expected: host.deactivate("ce-demo") is true
   - Expected: host.resolve_custom_editor("demo.kind").extension_name equals ``
   - Expected: host.resolve_custom_editor("sibling.kind").extension_name equals `ce-sibling-demo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("deactivating one extension leaves a sibling extension's custom editor bound")
val host = ExtensionHost.new()
host.register_manifest(ce_demo_manifest(), "<test>")
host.register_manifest(ce_sibling_manifest(), "<test>")
host.activate("ce-demo")
host.activate("ce-sibling-demo")
expect(host.resolve_custom_editor("demo.kind").extension_name).to_equal("ce-demo")
expect(host.resolve_custom_editor("sibling.kind").extension_name).to_equal("ce-sibling-demo")

expect(host.deactivate("ce-demo")).to_equal(true)
expect(host.resolve_custom_editor("demo.kind").extension_name).to_equal("")
expect(host.resolve_custom_editor("sibling.kind").extension_name).to_equal("ce-sibling-demo")
```

</details>

#### resolves the highest-priority editor when two extensions declare the same document_kind

- resolves the highest-priority editor when two extensions declare the same document_kind
   - Expected: resolved.extension_name equals `ce-high-demo`
   - Expected: resolved.editor.priority equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves the highest-priority editor when two extensions declare the same document_kind")
val host = ExtensionHost.new()
host.register_manifest(ce_low_priority_manifest(), "<test>")
host.register_manifest(ce_high_priority_manifest(), "<test>")
host.activate("ce-low-demo")
host.activate("ce-high-demo")
val resolved = host.resolve_custom_editor("shared.kind")
expect(resolved.extension_name).to_equal("ce-high-demo")
expect(resolved.editor.priority).to_equal(5)
```

</details>

#### falls back to the remaining editor once the higher-priority one is deactivated

- falls back to the remaining editor once the higher-priority one is deactivated
   - Expected: host.deactivate("ce-high-demo") is true
   - Expected: resolved.extension_name equals `ce-low-demo`
   - Expected: resolved.editor.priority equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to the remaining editor once the higher-priority one is deactivated")
val host = ExtensionHost.new()
host.register_manifest(ce_low_priority_manifest(), "<test>")
host.register_manifest(ce_high_priority_manifest(), "<test>")
host.activate("ce-low-demo")
host.activate("ce-high-demo")
expect(host.deactivate("ce-high-demo")).to_equal(true)
val resolved = host.resolve_custom_editor("shared.kind")
expect(resolved.extension_name).to_equal("ce-low-demo")
expect(resolved.editor.priority).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/custom_editor_contribution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering extension manifest contributes_custom_editors binds into a resolvable registry.
- extension manifest contributes_custom_editors binds into a resolvable registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `514da247679049a7554b5a93cf963549deaec9a393668688fdaa465fe059e7ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `514da247679049a7554b5a93cf963549deaec9a393668688fdaa465fe059e7ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `514da247679049a7554b5a93cf963549deaec9a393668688fdaa465fe059e7ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/lib/editor/custom_editor_contribution_spec.spl
mirror: doc/06_spec/01_unit/lib/editor/custom_editor_contribution_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=95 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/editor/custom_editor_contribution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/editor/custom_editor_contribution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/editor/custom_editor_contribution_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/editor/custom_editor_contribution_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'is unresolved before activation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/editor/custom_editor_contribution_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is unresolved before activation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/custom_editor_contribution_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the contributed custom editor on activate, resolvable by document_kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/custom_editor_contribution_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reverses the binding on deactivate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
