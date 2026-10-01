# Focus Tab Index Specification

> Tests covering focus traversal honors tab_index.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Focus Tab Index Specification

## Scenarios

### focus traversal honors tab_index

#### orders widgets by tab_index (1,2,3) not declaration order

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- orders widgets by tab_index (1,2,3) not declaration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders widgets by tab_index (1,2,3) not declaration order")
val order = get_focusable_ordered(tab_state().tree)
val pb = index_of(order, "tab_b")
val pc = index_of(order, "tab_c")
val pa = index_of(order, "tab_a")
assert_true(pb < pc)
assert_true(pc < pa)
```

</details>

#### focus_next steps through the widgets in tab order

- focus_next steps through the widgets in tab order
   - Expected: s.focused_id equals `tab_c`
   - Expected: s.focused_id equals `tab_a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("focus_next steps through the widgets in tab order")
# Focus tab_b, then Next should land on tab_c (next tab_index), then tab_a.
var s = tab_state()
s = UIState(tree: s.tree, mode: s.mode, focused_id: "tab_b", command_buffer: s.command_buffer)
s = focus_next(s)
expect(s.focused_id).to_equal("tab_c")
s = focus_next(s)
expect(s.focused_id).to_equal("tab_a")
```

</details>

#### focus_prev reverses the tab order

- focus_prev reverses the tab order
   - Expected: s.focused_id equals `tab_c`
   - Expected: s.focused_id equals `tab_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("focus_prev reverses the tab order")
var s = tab_state()
s = UIState(tree: s.tree, mode: s.mode, focused_id: "tab_a", command_buffer: s.command_buffer)
s = focus_prev(s)
expect(s.focused_id).to_equal("tab_c")
s = focus_prev(s)
expect(s.focused_id).to_equal("tab_b")
```

</details>

#### widgets without tab_index keep declaration position as their key

- widgets without tab_index keep declaration position as their key


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("widgets without tab_index keep declaration position as their key")
# No tab_index props at all: order equals declaration order.
val root = column("plainroot", [
    button("plain_a", "A", "a"),
    button("plain_b", "B", "b"),
])
val order = get_focusable_ordered(build_tree(root))
assert_true(index_of(order, "plain_a") < index_of(order, "plain_b"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/focus_tab_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering focus traversal honors tab_index.
- focus traversal honors tab_index

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

- Canonical SPipe generation for source `b1a685b5d56e84a040d019e00f3538d5a4db2716bb14b7ed34ec27bfc5517b0e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1a685b5d56e84a040d019e00f3538d5a4db2716bb14b7ed34ec27bfc5517b0e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1a685b5d56e84a040d019e00f3538d5a4db2716bb14b7ed34ec27bfc5517b0e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/focus_tab_index_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/focus_tab_index_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/focus_tab_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/focus_tab_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/focus_tab_index_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders widgets by tab_index (1,2,3) not declaration order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/focus_tab_index_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'focus_next steps through the widgets in tab order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/focus_tab_index_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'focus_prev reverses the tab order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
