# Keybinding Contribution Specification

> Tests covering extension manifest contributes_keybindings binds into the KeybindingManager.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Keybinding Contribution Specification

## Scenarios

### extension manifest contributes_keybindings binds into the KeybindingManager

#### is unresolved before activation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is unresolved before activation
   - Expected: host.keybinding_resolve("Ctrl+Shift+K", "normal") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is unresolved before activation")
val host = ExtensionHost.new()
host.register_manifest(kb_demo_manifest(), "<test>")
expect(host.keybinding_resolve("Ctrl+Shift+K", "normal")).to_equal("")
```

</details>

#### binds the contributed key to its command on activate

- binds the contributed key to its command on activate
   - Expected: host.activate("kb-demo") is true
   - Expected: host.keybinding_resolve("Ctrl+Shift+K", "normal") equals `kb.demo.ping`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("binds the contributed key to its command on activate")
val host = ExtensionHost.new()
host.register_manifest(kb_demo_manifest(), "<test>")
expect(host.activate("kb-demo")).to_equal(true)
expect(host.keybinding_resolve("Ctrl+Shift+K", "normal")).to_equal("kb.demo.ping")
```

</details>

#### reverses the binding on deactivate

- reverses the binding on deactivate
   - Expected: host.keybinding_resolve("Ctrl+Shift+K", "normal") equals `kb.demo.ping`
   - Expected: host.deactivate("kb-demo") is true
   - Expected: host.keybinding_resolve("Ctrl+Shift+K", "normal") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reverses the binding on deactivate")
val host = ExtensionHost.new()
host.register_manifest(kb_demo_manifest(), "<test>")
host.activate("kb-demo")
expect(host.keybinding_resolve("Ctrl+Shift+K", "normal")).to_equal("kb.demo.ping")
expect(host.deactivate("kb-demo")).to_equal(true)
expect(host.keybinding_resolve("Ctrl+Shift+K", "normal")).to_equal("")
```

</details>

#### does not resolve in any mode after deactivate, then re-binds on re-activate

- does not resolve in any mode after deactivate, then re-binds on re-activate
   - Expected: host.keybinding_resolve("Ctrl+Shift+K", "insert") equals ``
   - Expected: host.activate("kb-demo") is true
   - Expected: host.keybinding_resolve("Ctrl+Shift+K", "normal") equals `kb.demo.ping`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not resolve in any mode after deactivate, then re-binds on re-activate")
val host = ExtensionHost.new()
host.register_manifest(kb_demo_manifest(), "<test>")
host.activate("kb-demo")
host.deactivate("kb-demo")
expect(host.keybinding_resolve("Ctrl+Shift+K", "insert")).to_equal("")
expect(host.activate("kb-demo")).to_equal(true)
expect(host.keybinding_resolve("Ctrl+Shift+K", "normal")).to_equal("kb.demo.ping")
```

</details>

#### deactivating one extension leaves a sibling extension's keybinding bound

- deactivating one extension leaves a sibling extension's keybinding bound
   - Expected: host.keybinding_resolve("Ctrl+Shift+K", "normal") equals `kb.demo.ping`
   - Expected: host.keybinding_resolve("Ctrl+Shift+J", "normal") equals `kb.sibling.ping`
   - Expected: host.deactivate("kb-demo") is true
   - Expected: host.keybinding_resolve("Ctrl+Shift+K", "normal") equals ``
   - Expected: host.keybinding_resolve("Ctrl+Shift+J", "normal") equals `kb.sibling.ping`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("deactivating one extension leaves a sibling extension's keybinding bound")
val host = ExtensionHost.new()
host.register_manifest(kb_demo_manifest(), "<test>")
host.register_manifest(kb_sibling_manifest(), "<test>")
host.activate("kb-demo")
host.activate("kb-sibling-demo")
expect(host.keybinding_resolve("Ctrl+Shift+K", "normal")).to_equal("kb.demo.ping")
expect(host.keybinding_resolve("Ctrl+Shift+J", "normal")).to_equal("kb.sibling.ping")

expect(host.deactivate("kb-demo")).to_equal(true)
expect(host.keybinding_resolve("Ctrl+Shift+K", "normal")).to_equal("")
expect(host.keybinding_resolve("Ctrl+Shift+J", "normal")).to_equal("kb.sibling.ping")
```

</details>

#### a builtin key still resolves unchanged when no contribution overrides it

- a builtin key still resolves unchanged when no contribution overrides it
   - Expected: host.keybinding_resolve("h", "normal") equals `move-left`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a builtin key still resolves unchanged when no contribution overrides it")
val host = ExtensionHost.new()
host.register_manifest(kb_demo_manifest(), "<test>")
host.activate("kb-demo")
expect(host.keybinding_resolve("h", "normal")).to_equal("move-left")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/keybinding_contribution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering extension manifest contributes_keybindings binds into the KeybindingManager.
- extension manifest contributes_keybindings binds into the KeybindingManager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `024800a37bb4c817d1dfdb92dd70364cfa53e4f01d0b0e58a595d2b7e592eee1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `024800a37bb4c817d1dfdb92dd70364cfa53e4f01d0b0e58a595d2b7e592eee1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `024800a37bb4c817d1dfdb92dd70364cfa53e4f01d0b0e58a595d2b7e592eee1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/lib/editor/keybinding_contribution_spec.spl
mirror: doc/06_spec/01_unit/lib/editor/keybinding_contribution_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/editor/keybinding_contribution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/editor/keybinding_contribution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/editor/keybinding_contribution_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'is unresolved before activation' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/editor/keybinding_contribution_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is unresolved before activation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/keybinding_contribution_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the contributed key to its command on activate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/keybinding_contribution_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reverses the binding on deactivate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
