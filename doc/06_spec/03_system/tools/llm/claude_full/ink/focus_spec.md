# Claude Full Focus Manager

> Purpose: should dispatch blur and focus when active element changes

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Focus Manager

Purpose: should dispatch blur and focus when active element changes

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/focus_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should dispatch blur and focus when active element changes
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Focus Manager

Mirrors the Ink root-owned focus manager and focus stack behavior.

## Scenarios

### Claude full focus manager

#### should dispatch blur and focus when active element changes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should dispatch blur and focus when active element changes
- Verify: should dispatch blur and focus when active element changes
- Focus two nodes in order
   - Expected: manager.activeElement equals `second`
   - Expected: manager.focusStack.len() equals `1`
   - Expected: manager.focusStack[0] equals `first`
   - Expected: manager.dispatchLog[0] equals `first:focus:`
   - Expected: manager.dispatchLog[1] equals `first:blur:second`
   - Expected: manager.dispatchLog[2] equals `second:focus:first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should dispatch blur and focus when active element changes")
step("Verify: should dispatch blur and focus when active element changes")
# @req: REQ-TOOLS-Focu-001
step("Focus two nodes in order")
val manager = demoFocusTree()
manager.focus("first")
manager.focus("second")
expect(manager.activeElement).to_equal("second")
expect(manager.focusStack.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(manager.focusStack[0]).to_equal("first")
expect(manager.dispatchLog[0]).to_equal("first:focus:")
expect(manager.dispatchLog[1]).to_equal("first:blur:second")
expect(manager.dispatchLog[2]).to_equal("second:focus:first")
```

</details>

#### should ignore focus requests while disabled and blur active focus

- should ignore focus requests while disabled and blur active focus
- Verify: should ignore focus requests while disabled and blur active focus
- Disable the manager before a focus request
   - Expected: manager.activeElement equals ``
   - Expected: manager.activeElement equals ``
   - Expected: manager.dispatchLog[1] equals `first:blur:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should ignore focus requests while disabled and blur active focus")
step("Verify: should ignore focus requests while disabled and blur active focus")
# @req: REQ-TOOLS-Focu-001
step("Disable the manager before a focus request")
val manager = demoFocusTree()
manager.disable()
manager.focus("first")
expect(manager.activeElement).to_equal("")
manager.enable()
manager.focus("first")
manager.blur()
expect(manager.activeElement).to_equal("")
expect(manager.dispatchLog[1]).to_equal("first:blur:")
```

</details>

#### should focus only click targets with numeric tab index

- should focus only click targets with numeric tab index
- Verify: should focus only click targets with numeric tab index
- Click a non-tabbable node and then a tabbable node
   - Expected: manager.activeElement equals ``
   - Expected: manager.activeElement equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should focus only click targets with numeric tab index")
step("Verify: should focus only click targets with numeric tab index")
# @req: REQ-TOOLS-Focu-001
step("Click a non-tabbable node and then a tabbable node")
val manager = demoFocusTree()
manager.handleClickFocus("plain")
expect(manager.activeElement).to_equal("")
manager.handleClickFocus("first")
expect(manager.activeElement).to_equal("first")
```

</details>

#### should move focus through tabbable nodes in tree order

- should move focus through tabbable nodes in tree order
- Verify: should move focus through tabbable nodes in tree order
- Cycle forward and backward through tabbable nodes
   - Expected: manager.activeElement equals `first`
   - Expected: manager.activeElement equals `second`
   - Expected: manager.activeElement equals `first`
   - Expected: manager.collectTabbable("root").len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should move focus through tabbable nodes in tree order")
step("Verify: should move focus through tabbable nodes in tree order")
# @req: REQ-TOOLS-Focu-001
step("Cycle forward and backward through tabbable nodes")
val manager = demoFocusTree()
manager.focusNext("root")
expect(manager.activeElement).to_equal("first")
manager.focusNext("root")
expect(manager.activeElement).to_equal("second")
manager.focusPrevious("root")
expect(manager.activeElement).to_equal("first")
expect(manager.collectTabbable("root").len()).to_equal(3)  # oracle: value fixed by the spec contract
```

</details>

#### should restore the most recent mounted focus when the active node is removed

- should restore the most recent mounted focus when the active node is removed
- Verify: should restore the most recent mounted focus when the active node is removed
- Remove the active node and restore from the focus stack
   - Expected: manager.activeElement equals `first`
   - Expected: manager.dispatchLog[3] equals `nested:blur:`
   - Expected: manager.dispatchLog[4] equals `first:focus:nested`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should restore the most recent mounted focus when the active node is removed")
step("Verify: should restore the most recent mounted focus when the active node is removed")
# @req: REQ-TOOLS-Focu-001
step("Remove the active node and restore from the focus stack")
val manager = demoFocusTree()
manager.focus("first")
manager.focus("nested")
manager.handleNodeRemoved("nested", "root")
expect(manager.activeElement).to_equal("first")
expect(manager.dispatchLog[3]).to_equal("nested:blur:")
expect(manager.dispatchLog[4]).to_equal("first:focus:nested")
```

</details>

#### should find the root node that owns the focus manager

- should find the root node that owns the focus manager
- Verify: should find the root node that owns the focus manager
- Walk from a descendant to the focus-manager root
   - Expected: manager.isInTree("nested", "root") is true
   - Expected: manager.getRootNode("nested") equals `root`
   - Expected: manager.getFocusManagerRoot("nested") equals `root`
   - Expected: maxFocusStack() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should find the root node that owns the focus manager")
step("Verify: should find the root node that owns the focus manager")
# @req: REQ-TOOLS-Focu-001
step("Walk from a descendant to the focus-manager root")
val manager = demoFocusTree()
expect(manager.isInTree("nested", "root")).to_equal(true)
expect(manager.getRootNode("nested")).to_equal("root")
expect(manager.getFocusManagerRoot("nested")).to_equal("root")
expect(maxFocusStack()).to_equal(32)  # oracle: value fixed by the spec contract
```

</details>

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

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Focu-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `216cb401937ca9035446873bcb127d24ce5a86eeacb26d2c7a5943098a4a2f68`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `216cb401937ca9035446873bcb127d24ce5a86eeacb26d2c7a5943098a4a2f68`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `216cb401937ca9035446873bcb127d24ce5a86eeacb26d2c7a5943098a4a2f68`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/ink/focus_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/focus_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/focus_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/focus_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/focus_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should dispatch blur and focus when active element changes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/focus_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should dispatch blur and focus when active element changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/focus_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should ignore focus requests while disabled and blur active focus' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/focus_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should ignore focus requests while disabled and blur active focus' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/focus_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should focus only click targets with numeric tab index' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/focus_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should focus only click targets with numeric tab index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/focus_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should move focus through tabbable nodes in tree order' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/focus_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should restore the most recent mounted focus when the active node is removed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/focus_spec.spl:108:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should find the root node that owns the focus manager' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
