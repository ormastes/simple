# Widget Keybindings Specification

> Tests covering with_keybindings registers real bindings.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget Keybindings Specification

## Scenarios

### with_keybindings registers real bindings

#### round-trips a binding through bindings()

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips a binding through bindings()
   - Expected: mode_map["g"] equals `focus_next`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a binding through bindings()")
val tree = build_tree(column("rtroot", [button("rt_b", "B", "b")]))
    .with_keybindings({"normal": {"g": "focus_next"}})
val all = tree.bindings()
assert_true(all.contains_key("normal"))
val mode_map = all["normal"]
assert_true(mode_map.contains_key("g"))
expect(mode_map["g"]).to_equal("focus_next")
```

</details>

#### a bound key fires its action instead of the default no-op

- a bound key fires its action instead of the default no-op
   - Expected: after.focused_id equals `kb_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a bound key fires its action instead of the default no-op")
# In Normal mode the plain key 'g' is a no-op; binding it to focus_next
# must move focus when pressed.
var s = kb_root()
val bound_tree = s.tree.with_keybindings({"normal": {"g": "focus_next"}})
s = UIState(tree: bound_tree, mode: s.mode, focused_id: "kbroot", command_buffer: s.command_buffer)
val after = process_event(s, UIEvent.KeyPress(key: "g"))
# focus advanced off the root to the first focusable child.
expect(after.focused_id).to_equal("kb_first")
```

</details>

#### an unbound tree leaves the same key as a no-op

- an unbound tree leaves the same key as a no-op
   - Expected: after.focused_id equals `kbroot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unbound tree leaves the same key as a no-op")
var s = kb_root()
s = UIState(tree: s.tree, mode: s.mode, focused_id: "kbroot", command_buffer: s.command_buffer)
val after = process_event(s, UIEvent.KeyPress(key: "g"))
expect(after.focused_id).to_equal("kbroot")
```

</details>

#### keeps bindings for multiple modes distinct

- keeps bindings for multiple modes distinct
   - Expected: m["escape"] equals `normal_mode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps bindings for multiple modes distinct")
val tree = build_tree(column("mmroot", [button("mm_b", "B", "b")]))
    .with_keybindings({"normal": {"g": "focus_next"}, "insert": {"escape": "normal_mode"}})
val all = tree.bindings()
assert_true(all.contains_key("insert"))
val m = all["insert"]
assert_true(m.contains_key("escape"))
expect(m["escape"]).to_equal("normal_mode")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/widget_keybindings_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering with_keybindings registers real bindings.
- with_keybindings registers real bindings

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

- Canonical SPipe generation for source `1add63aa66dbb29c5965f1f8719707cddb876131a4358ae6ceefea613ed3a470`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1add63aa66dbb29c5965f1f8719707cddb876131a4358ae6ceefea613ed3a470`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1add63aa66dbb29c5965f1f8719707cddb876131a4358ae6ceefea613ed3a470`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/widget_keybindings_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/widget_keybindings_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/widget_keybindings_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/widget_keybindings_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/widget_keybindings_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a binding through bindings()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/widget_keybindings_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a bound key fires its action instead of the default no-op' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/widget_keybindings_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'an unbound tree leaves the same key as a no-op' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
