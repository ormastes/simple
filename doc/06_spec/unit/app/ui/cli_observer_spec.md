# Cli Observer Specification

> Tests covering CLIObserver render_summary, CLIObserver render_changes, CLIObserver render_adaptive, CLIObserver render_tree_outline, render_node_outline.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Observer Specification

## Scenarios

### CLIObserver render_summary

#### includes mode and focused widget

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- includes mode and focused widget


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes mode and focused widget")
val root = column("cli_obs_root1", [
    text_widget("cli_obs_t1", "Hello")
])
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new(session)
val summary = observer.render_summary()
expect summary to_contain "NORMAL"
expect summary to_contain "STATE (observer)"
```

</details>

#### includes viewport description

- includes viewport description


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes viewport description")
val root = text_widget("cli_obs_vp_root", "VP")
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new(session)
val summary = observer.render_summary()
expect summary to_contain "80x24"
```

</details>

#### lists surfaces

- lists surfaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists surfaces")
val root = text_widget("cli_obs_surf_root", "Main")
val tree = UITree.new(root)
var session = new_session(tree)
val popup_root = text_widget("cli_obs_popup_r", "Popup")
val popup_tree = UITree.new(popup_root)
session.open_surface("popup", popup_tree)
val observer = CLIObserver.new(session)
val summary = observer.render_summary()
expect summary to_contain "main"
expect summary to_contain "popup"
```

</details>

### CLIObserver render_changes

#### shows no recent changes for fresh session

- shows no recent changes for fresh session


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows no recent changes for fresh session")
val root = text_widget("cli_obs_chg_root", "Fresh")
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new(session)
val output = observer.render_changes(5)
expect output to_contain "No recent changes"
```

</details>

#### shows changes after tree update

- shows changes after tree update


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows changes after tree update")
val root1 = column("cli_obs_chg_upd", [
    text_widget("cli_obs_chg_t1", "Old")
])
val tree1 = UITree.new(root1)
var session = new_session(tree1)
val root2 = column("cli_obs_chg_upd", [
    text_widget("cli_obs_chg_t1", "Old"),
    text_widget("cli_obs_chg_t2", "New")
])
val tree2 = UITree.new(root2)
session.update_tree(tree2)
val observer = CLIObserver.new(session)
val output = observer.render_changes(10)
expect output to_contain "Recent changes"
```

</details>

### CLIObserver render_adaptive

#### renders tiny mode for small line budget

- renders tiny mode for small line budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders tiny mode for small line budget")
val root = text_widget("cli_obs_ada_tiny", "Tiny")
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new_with_lines(session, 3)
val output = observer.render_adaptive()
expect output to_contain "mode:"
expect output to_contain "NORMAL"
```

</details>

#### renders medium mode for mid-range budget

- renders medium mode for mid-range budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders medium mode for mid-range budget")
val root = text_widget("cli_obs_ada_mid", "Mid")
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new_with_lines(session, 8)
val output = observer.render_adaptive()
expect output to_contain "STATE (observer)"
```

</details>

#### renders full mode for large budget

- renders full mode for large budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders full mode for large budget")
val root = text_widget("cli_obs_ada_full", "Full")
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new_with_lines(session, 30)
val output = observer.render_adaptive()
expect output to_contain "surfaces"
```

</details>

### CLIObserver render_tree_outline

#### renders root node

- renders root node


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders root node")
val root = text_widget("cli_obs_tree_root", "Root")
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new(session)
val outline = observer.render_tree_outline()
expect outline to_contain "cli_obs_tree_root"
```

</details>

#### renders nested children with indentation

- renders nested children with indentation


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders nested children with indentation")
val root = column("cli_obs_tree_nest", [
    text_widget("cli_obs_tree_c1", "Child1"),
    text_widget("cli_obs_tree_c2", "Child2")
])
val tree = UITree.new(root)
val session = new_session(tree)
val observer = CLIObserver.new(session)
val outline = observer.render_tree_outline()
expect outline to_contain "cli_obs_tree_nest"
expect outline to_contain "cli_obs_tree_c1"
expect outline to_contain "cli_obs_tree_c2"
```

</details>

### render_node_outline

#### indents based on depth

- indents based on depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("indents based on depth")
val node = text_widget("cli_rno_node", "Test")
val output = render_node_outline(node, 2)
expect output to_start_with "    "
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/cli_observer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CLIObserver render_summary, CLIObserver render_changes, CLIObserver render_adaptive, CLIObserver render_tree_outline, render_node_outline.
- CLIObserver render_summary
- CLIObserver render_changes
- CLIObserver render_adaptive
- CLIObserver render_tree_outline
- render_node_outline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `a476028d7e62ffc5f63e4a130171b9a63042aa70774664c9d6b916d42007af9d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a476028d7e62ffc5f63e4a130171b9a63042aa70774664c9d6b916d42007af9d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a476028d7e62ffc5f63e4a130171b9a63042aa70774664c9d6b916d42007af9d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/cli_observer_spec.spl
mirror: doc/06_spec/unit/app/ui/cli_observer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/cli_observer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/cli_observer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/cli_observer_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes mode and focused widget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/cli_observer_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes viewport description' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/cli_observer_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
