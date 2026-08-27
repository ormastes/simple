# Aggregator Walker Specification

> Tests covering aggregator_walker.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aggregator Walker Specification

## Scenarios

### aggregator_walker

#### walk_referenced_surfaces returns empty list when root has no referenced surfaces

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- walk_referenced_surfaces returns empty list when root has no referenced surfaces


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("walk_referenced_surfaces returns empty list when root has no referenced surfaces")
val root = _empty_frame([])
val ctx = _context_with([])
val result = walk_referenced_surfaces(root, ctx)
val result_len = result.len()
result_len.to_equal(0)
```

</details>

#### walk_referenced_surfaces returns one id when root references one child

- walk_referenced_surfaces returns one id when root references one child


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("walk_referenced_surfaces returns one id when root references one child")
val child_sid = _sid(2, 0)
val root = _empty_frame([child_sid])
val child_frame = _empty_frame([])
val ctx = _context_with([_entry(child_sid, child_frame)])
val result = walk_referenced_surfaces(root, ctx)
val result_len = result.len()
result_len.to_equal(1)
val found = result[0]
val eq = found.equals(child_sid)
eq.to_equal(true)
```

</details>

#### walk_referenced_surfaces terminates and dedups on a cycle A to B to A

- walk_referenced_surfaces terminates and dedups on a cycle A to B to A


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("walk_referenced_surfaces terminates and dedups on a cycle A to B to A")
val sid_a = _sid(10, 0)
val sid_b = _sid(11, 0)
# A references B, B references A — cycle
val frame_a = _empty_frame([sid_b])
val frame_b = _empty_frame([sid_a])
val root = _empty_frame([sid_a])
val ctx = _context_with([
    _entry(sid_a, frame_a),
    _entry(sid_b, frame_b)
])
val result = walk_referenced_surfaces(root, ctx)
# Should see each of sid_a, sid_b exactly once
val result_len = result.len()
result_len.to_equal(2)
```

</details>

#### find_frame_for returns Some when id is in context

- find_frame_for returns Some when id is in context


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("find_frame_for returns Some when id is in context")
val sid = _sid(1, 0)
val frame = _empty_frame([])
val ctx = _context_with([_entry(sid, frame)])
val maybe = find_frame_for(ctx, sid)
if val Some(f) = maybe:
    val ref_len = f.referenced_surfaces.len()
    ref_len.to_equal(0)
else:
    # force failure: should have found it
    true.to_equal(false)
```

</details>

#### find_frame_for returns None when id is not in context

- find_frame_for returns None when id is not in context


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("find_frame_for returns None when id is not in context")
# Verify by empty context: find_frame_for on a fresh empty context always returns None.
# Use walk_referenced_surfaces to indirectly confirm: if find_frame_for correctly
# returns None for the unknown_sid, walk won't recurse into it (no child frame).
val unknown_sid = _sid(99, 0)
val ctx = _context_with([])
val root_frame = _empty_frame([unknown_sid])
val result = walk_referenced_surfaces(root_frame, ctx)
# walk adds unknown_sid to result (it's referenced), but since find_frame_for
# returns None there are no children to add. Result length = 1.
val result_len = result.len()
result_len.to_equal(1)
```

</details>

#### inline_render_pass appends child quads to parent quads

- inline_render_pass appends child quads to parent quads


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("inline_render_pass appends child quads to parent quads")
val parent_sqs = [_sqs()]
val parent_quads = [_solid_quad(0)]
val parent_pass = _pass_with_quads(1, parent_quads, parent_sqs)

val child_sqs = [_sqs(), _sqs()]
val child_quads = [_solid_quad(0), _solid_quad(1), _solid_quad(1)]
val child_frame = _frame_with_one_pass([], 2, child_quads, child_sqs)

val result = inline_render_pass(parent_pass, child_frame)
# parent had 1 quad, child has 3 → merged has 4
val merged_len = result.quads.len()
merged_len.to_equal(4)
```

</details>

#### inline_render_pass remaps child sqs indices by parent sqs count offset

- inline_render_pass remaps child sqs indices by parent sqs count offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("inline_render_pass remaps child sqs indices by parent sqs count offset")
val parent_sqs = [_sqs(), _sqs()]   # 2 parent sqs → offset = 2
val parent_quads = [_solid_quad(0), _solid_quad(1)]
val parent_pass = _pass_with_quads(1, parent_quads, parent_sqs)

val child_sqs = [_sqs()]
# child quad references sqs index 0 in child's sqs list
val child_quads = [_solid_quad(0)]
val child_frame = _frame_with_one_pass([], 2, child_quads, child_sqs)

val result = inline_render_pass(parent_pass, child_frame)
# The appended (3rd) quad was child quad at sqs index 0, remapped to 0+2=2
val merged_third_quad = result.quads[2]
merged_third_quad.shared_quad_state_index.to_equal(2)
```

</details>

#### drop_missing_surface removes RenderPass quads matching hint and preserves others

- drop_missing_surface removes RenderPass quads matching hint and preserves others


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drop_missing_surface removes RenderPass quads matching hint and preserves others")
val sqs_list = [_sqs()]
# One solid-color quad (not a RenderPass quad) and one RenderPass quad with pass_id=42
val solid = _solid_quad(0)
val rp_quad = _render_pass_quad(0, 42)
val render_pass = _pass_with_quads(1, [solid, rp_quad], sqs_list)

val result = drop_missing_surface(render_pass, "42")
# RenderPass quad with render_pass_id==42 should be dropped; solid kept
val kept_len = result.quads.len()
kept_len.to_equal(1)
val kept = result.quads[0]
val is_solid = if kept.kind == DrawQuadKind.SolidColor: true else: false
is_solid.to_equal(true)
```

</details>

#### drop_missing_surface returns all quads unchanged when no quad matches hint

- drop_missing_surface returns all quads unchanged when no quad matches hint


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("drop_missing_surface returns all quads unchanged when no quad matches hint")
val sqs_list = [_sqs()]
val solid1 = _solid_quad(0)
val solid2 = _solid_quad(0)
val render_pass = _pass_with_quads(1, [solid1, solid2], sqs_list)

val result = drop_missing_surface(render_pass, "99")
val unchanged_len = result.quads.len()
unchanged_len.to_equal(2)
```

</details>

#### placeholder_deferred_surface returns pass with same quad count

- placeholder_deferred_surface returns pass with same quad count


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("placeholder_deferred_surface returns pass with same quad count")
val sqs_list = [_sqs()]
val quads = [_solid_quad(0), _solid_quad(0)]
val render_pass = _pass_with_quads(1, quads, sqs_list)
val sid = _sid(5, 0)

val result = placeholder_deferred_surface(render_pass, sid)
val deferred_len = result.quads.len()
deferred_len.to_equal(2)
result.id.to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/viz/aggregator_walker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering aggregator_walker.
- aggregator_walker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `954f79499befaf69ba16ef9209775eb98145bc0ddc4a92614abdf29f3b3bfa24`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `954f79499befaf69ba16ef9209775eb98145bc0ddc4a92614abdf29f3b3bfa24`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `954f79499befaf69ba16ef9209775eb98145bc0ddc4a92614abdf29f3b3bfa24`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/viz/aggregator_walker_spec.spl
mirror: doc/06_spec/01_unit/lib/viz/aggregator_walker_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/lib/viz/aggregator_walker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/viz/aggregator_walker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/viz/aggregator_walker_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/lib/viz/aggregator_walker_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/viz/aggregator_walker_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'walk_referenced_surfaces returns empty list when root has no referenced surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/viz/aggregator_walker_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'walk_referenced_surfaces returns one id when root references one child' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/viz/aggregator_walker_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'walk_referenced_surfaces terminates and dedups on a cycle A to B to A' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
