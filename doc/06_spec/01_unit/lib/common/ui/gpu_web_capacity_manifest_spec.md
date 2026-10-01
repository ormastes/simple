# gpu_web_capacity_manifest_spec

> Purpose: Prove that GPU web capacity manifest (Kernel C).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_web_capacity_manifest_spec

Purpose: Prove that GPU web capacity manifest (Kernel C).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that GPU web capacity manifest (Kernel C).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### GPU web capacity manifest (Kernel C)

#### should accept a plan that fits inside every bound

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Verify a small plan against the compile-time default manifest
   - Expected: verdict.accepted is true
   - Expected: verdict.breach_count equals `0`
   - Expected: verdict.reason equals ``
   - Expected: verdict.first_breach_bound equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-COMMON-001
step("Verify a small plan against the compile-time default manifest")
val manifest = gpu_web_capacity_manifest_compile_time_default()
var plan = gpu_web_capacity_plan_zero()
plan.input_bytes = 4096u64
plan.nodes = 120u32
plan.attributes = 300u32
plan.dom_edges = 119u32
plan.string_bytes = 2048u64
plan.computed_styles = 120u32
plan.glyphs = 900u32
plan.events_in_flight = 4u32
plan.route_depth = 12u16
plan.draw_batches = 6u32
plan.draw_commands = 240u32
val verdict = gpu_web_capacity_verify(plan, manifest)
expect(verdict.accepted).to_equal(true)
expect(verdict.breach_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(verdict.reason).to_equal("")
expect(verdict.first_breach_bound).to_equal("")
```

</details>

#### should accept a plan that sits exactly at capacity

- should accept a plan that sits exactly at capacity
- Set every exercised total to its exact bound
   - Expected: verdict.breach_count equals `0`
   - Expected: verdict.accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should accept a plan that sits exactly at capacity")
step("Set every exercised total to its exact bound")
val manifest = gpu_web_capacity_manifest_compile_time_default()
var plan = gpu_web_capacity_plan_zero()
plan.input_bytes = manifest.max_input_bytes
plan.nodes = manifest.max_nodes
plan.attributes = manifest.max_attributes
plan.dom_edges = manifest.max_dom_edges
plan.string_bytes = manifest.max_string_bytes
plan.computed_styles = manifest.max_computed_styles
plan.glyphs = manifest.max_glyphs
plan.events_in_flight = manifest.max_events_in_flight
plan.route_depth = manifest.max_route_depth
plan.draw_batches = manifest.max_draw_batches
plan.draw_commands = manifest.max_draw_commands
val verdict = gpu_web_capacity_verify(plan, manifest)
expect(verdict.breach_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(verdict.accepted).to_equal(true)
```

</details>

#### should reject one node over capacity and name the bound

- should reject one node over capacity and name the bound
- Exceed max_nodes by exactly one record
   - Expected: verdict.accepted is false
   - Expected: verdict.breach_count equals `1`
   - Expected: verdict.first_breach_bound equals `max_nodes`
   - Expected: verdict.breaches[0].overflow equals `1`
   - Expected: verdict.breaches[0].limit equals `65536`
   - Expected: verdict.breaches[0].requested equals `65537`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject one node over capacity and name the bound")
step("Exceed max_nodes by exactly one record")
val manifest = gpu_web_capacity_manifest_compile_time_default()
var plan = gpu_web_capacity_plan_zero()
plan.nodes = (manifest.max_nodes.to_i64() + 1).to_u32()
val verdict = gpu_web_capacity_verify(plan, manifest)
expect(verdict.accepted).to_equal(false)
expect(verdict.breach_count).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(verdict.first_breach_bound).to_equal("max_nodes")
expect(verdict.breaches[0].overflow).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(verdict.breaches[0].limit).to_equal(65536)  # oracle: 65536 — named expected value from the requirement
expect(verdict.breaches[0].requested).to_equal(65537)  # oracle: 65537 — named expected value from the requirement
```

</details>

#### should carry a reason receipt naming bound, request, limit and overflow

- should carry a reason receipt naming bound, request, limit and overflow
- Read the full rejection receipt for a single breach
   - Expected: verdict.reason equals `gpu_web_capacity_exceeded: max_glyphs requested=5000 limit=4096 over=904`
   - Expected: gpu_web_capacity_breach_receipt(verdict.breaches[0]) equals `max_glyphs requested=5000 limit=4096 over=904`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should carry a reason receipt naming bound, request, limit and overflow")
step("Read the full rejection receipt for a single breach")
val manifest = gpu_web_capacity_manifest_compile_time_default()
var plan = gpu_web_capacity_plan_zero()
plan.glyphs = 5000u32
val verdict = gpu_web_capacity_verify(plan, manifest)
expect(verdict.reason).to_equal("gpu_web_capacity_exceeded: max_glyphs requested=5000 limit=4096 over=904")
expect(gpu_web_capacity_breach_receipt(verdict.breaches[0])).to_equal("max_glyphs requested=5000 limit=4096 over=904")
```

</details>

#### should report every exceeded bound in frozen contract order

- should report every exceeded bound in frozen contract order
- Exceed a draw bound and a DOM bound at once
   - Expected: verdict.breach_count equals `2`
   - Expected: verdict.breaches[0].bound equals `max_nodes`
   - Expected: verdict.breaches[1].bound equals `max_draw_commands`
   - Expected: verdict.reason equals `gpu_web_capacity_exceeded: max_nodes requested=70000 limit=65536 over=4464; m... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should report every exceeded bound in frozen contract order")
step("Exceed a draw bound and a DOM bound at once")
val manifest = gpu_web_capacity_manifest_compile_time_default()
var plan = gpu_web_capacity_plan_zero()
plan.draw_commands = 2000u32
plan.nodes = 70000u32
val verdict = gpu_web_capacity_verify(plan, manifest)
expect(verdict.breach_count).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(verdict.breaches[0].bound).to_equal("max_nodes")
expect(verdict.breaches[1].bound).to_equal("max_draw_commands")
expect(verdict.reason).to_equal("gpu_web_capacity_exceeded: max_nodes requested=70000 limit=65536 over=4464; max_draw_commands requested=2000 limit=1024 over=976")
```

</details>

#### should reject rather than silently permit an unset bound

- should reject rather than silently permit an unset bound
- Request a resource whose bound the manifest never set
   - Expected: verdict.accepted is false
   - Expected: verdict.first_breach_bound equals `max_css_rules`
   - Expected: verdict.reason equals `gpu_web_capacity_exceeded: max_css_rules requested=1 limit=0 over=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject rather than silently permit an unset bound")
step("Request a resource whose bound the manifest never set")
val manifest = gpu_web_capacity_manifest_compile_time_default()
var plan = gpu_web_capacity_plan_zero()
plan.css_rules = 1u32
val verdict = gpu_web_capacity_verify(plan, manifest)
expect(verdict.accepted).to_equal(false)
expect(verdict.first_breach_bound).to_equal("max_css_rules")
expect(verdict.reason).to_equal("gpu_web_capacity_exceeded: max_css_rules requested=1 limit=0 over=1")
```

</details>

#### should accept an empty plan against a zero manifest

- should accept an empty plan against a zero manifest
- Reserve nothing and emit nothing
   - Expected: verdict.breach_count equals `0`
   - Expected: verdict.accepted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should accept an empty plan against a zero manifest")
step("Reserve nothing and emit nothing")
val verdict = gpu_web_capacity_verify(gpu_web_capacity_plan_zero(), gpu_web_capacity_manifest_zero())
expect(verdict.breach_count).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(verdict.accepted).to_equal(true)
```

</details>

#### should reject scratch-byte overruns with their own receipt

- should reject scratch-byte overruns with their own receipt
- Ask for parser scratch the manifest never reserved
   - Expected: verdict.first_breach_bound equals `parser_scratch_bytes`
   - Expected: verdict.reason equals `gpu_web_capacity_exceeded: parser_scratch_bytes requested=8193 limit=8192 over=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject scratch-byte overruns with their own receipt")
step("Ask for parser scratch the manifest never reserved")
var manifest = gpu_web_capacity_manifest_zero()
manifest.parser_scratch_bytes = 8192u64
var plan = gpu_web_capacity_plan_zero()
plan.parser_scratch_bytes = 8193u64
val verdict = gpu_web_capacity_verify(plan, manifest)
expect(verdict.first_breach_bound).to_equal("parser_scratch_bytes")
expect(verdict.reason).to_equal("gpu_web_capacity_exceeded: parser_scratch_bytes requested=8193 limit=8192 over=1")
```

</details>

#### should let a load-time response size tighten the input bound

- should let a load-time response size tighten the input bound
- Declare a response far smaller than the compile-time ceiling
   - Expected: tightened.max_input_bytes.to_i64() equals `4096`
   - Expected: tightened.max_string_bytes.to_i64() equals `4096`
- A plan that fit the compile-time bound is now rejected
   - Expected: gpu_web_capacity_verify(plan, base).accepted is true
   - Expected: after.first_breach_bound equals `max_input_bytes`
   - Expected: after.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should let a load-time response size tighten the input bound")
step("Declare a response far smaller than the compile-time ceiling")
val base = gpu_web_capacity_manifest_compile_time_default()
val tightened = gpu_web_capacity_manifest_for_load(base, 4096, 0, 0, 0)
expect(tightened.max_input_bytes.to_i64()).to_equal(4096)  # oracle: 4096 — named expected value from the requirement
expect(tightened.max_string_bytes.to_i64()).to_equal(4096)  # oracle: 4096 — named expected value from the requirement
step("A plan that fit the compile-time bound is now rejected")
var plan = gpu_web_capacity_plan_zero()
plan.input_bytes = 8192u64
expect(gpu_web_capacity_verify(plan, base).accepted).to_equal(true)
val after = gpu_web_capacity_verify(plan, tightened)
expect(after.first_breach_bound).to_equal("max_input_bytes")
expect(after.accepted).to_equal(false)
```

</details>

#### should never let a load-time hint raise a committed bound

- should never let a load-time hint raise a committed bound
- Declare a response larger than the compile-time ceiling
   - Expected: widened.max_input_bytes.to_i64() equals `base.max_input_bytes.to_i64()`
   - Expected: widened.max_string_bytes.to_i64() equals `base.max_string_bytes.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should never let a load-time hint raise a committed bound")
step("Declare a response larger than the compile-time ceiling")
val base = gpu_web_capacity_manifest_compile_time_default()
val widened = gpu_web_capacity_manifest_for_load(base, 999999999, 0, 0, 0)
expect(widened.max_input_bytes.to_i64()).to_equal(base.max_input_bytes.to_i64())
expect(widened.max_string_bytes.to_i64()).to_equal(base.max_string_bytes.to_i64())
```

</details>

#### should let a small viewport tighten the glyph bound

- should let a small viewport tighten the glyph bound
- Use a viewport that holds fewer cells than the glyph ceiling
   - Expected: tightened.max_glyphs.to_i64() equals `200`
- A large viewport leaves the committed bound alone
   - Expected: wide.max_glyphs.to_i64() equals `base.max_glyphs.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should let a small viewport tighten the glyph bound")
step("Use a viewport that holds fewer cells than the glyph ceiling")
val base = gpu_web_capacity_manifest_compile_time_default()
val tightened = gpu_web_capacity_manifest_for_load(base, 0, 160, 80, 8)
expect(tightened.max_glyphs.to_i64()).to_equal(200)  # oracle: 200 — named expected value from the requirement
step("A large viewport leaves the committed bound alone")
val wide = gpu_web_capacity_manifest_for_load(base, 0, 1920, 1080, 8)
expect(wide.max_glyphs.to_i64()).to_equal(base.max_glyphs.to_i64())
```

</details>

#### should take backend descriptor limits and preprocess requirements

- should take backend descriptor limits and preprocess requirements
- Create a session with a 512-command descriptor limit
   - Expected: session.max_draw_commands.to_i64() equals `512`
- The preprocess requirement is rounded up to the backend alignment
   - Expected: session.backend_preprocess_bytes.to_i64() equals `1024`
- A plan above the descriptor limit is rejected
   - Expected: verdict.first_breach_bound equals `max_draw_commands`
   - Expected: verdict.accepted is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should take backend descriptor limits and preprocess requirements")
step("Create a session with a 512-command descriptor limit")
val base = gpu_web_capacity_manifest_compile_time_default()
val session = gpu_web_capacity_manifest_for_backend_session(base, 256, 512, 1000)
expect(session.max_draw_commands.to_i64()).to_equal(512)  # oracle: 512 — named expected value from the requirement
step("The preprocess requirement is rounded up to the backend alignment")
expect(session.backend_preprocess_bytes.to_i64()).to_equal(1024)  # oracle: 1024 — named expected value from the requirement
step("A plan above the descriptor limit is rejected")
var plan = gpu_web_capacity_plan_zero()
plan.draw_commands = 600u32
val verdict = gpu_web_capacity_verify(plan, session)
expect(verdict.first_breach_bound).to_equal("max_draw_commands")
expect(verdict.accepted).to_equal(false)
```

</details>

#### should expose a stable rejection code on every receipt

- should expose a stable rejection code on every receipt
- Check the receipt prefix used by fallback accounting
   - Expected: verdict.reason.starts_with(GPU_WEB_CAPACITY_REJECT_CODE) is true
   - Expected: verdict.first_breach_bound equals `max_route_depth`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should expose a stable rejection code on every receipt")
step("Check the receipt prefix used by fallback accounting")
val manifest = gpu_web_capacity_manifest_compile_time_default()
var plan = gpu_web_capacity_plan_zero()
plan.route_depth = 1000u16
val verdict = gpu_web_capacity_verify(plan, manifest)
expect(verdict.reason.starts_with(GPU_WEB_CAPACITY_REJECT_CODE)).to_equal(true)
expect(verdict.first_breach_bound).to_equal("max_route_depth")
```

</details>

#### should bound host effects per epoch at the documented default

- should bound host effects per epoch at the documented default
- Read the per-epoch host-effect ceiling the default manifest commits to
   - Expected: manifest.max_host_effects_per_epoch.to_i64() equals `4`
- An epoch asking for exactly the ceiling is accepted
   - Expected: gpu_web_capacity_verify(at_bound, manifest).accepted is true
- One host effect past the ceiling is rejected by name
   - Expected: verdict.accepted is false
   - Expected: verdict.first_breach_bound equals `max_host_effects_per_epoch`
   - Expected: verdict.reason equals `gpu_web_capacity_exceeded: max_host_effects_per_epoch requested=5 limit=4 over=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should bound host effects per epoch at the documented default")
step("Read the per-epoch host-effect ceiling the default manifest commits to")
val manifest = gpu_web_capacity_manifest_compile_time_default()
expect(manifest.max_host_effects_per_epoch.to_i64()).to_equal(4)  # oracle: 4 — named expected value from the requirement
step("An epoch asking for exactly the ceiling is accepted")
var at_bound = gpu_web_capacity_plan_zero()
at_bound.host_effects_per_epoch = 4u32
expect(gpu_web_capacity_verify(at_bound, manifest).accepted).to_equal(true)
step("One host effect past the ceiling is rejected by name")
var over = gpu_web_capacity_plan_zero()
over.host_effects_per_epoch = 5u32
val verdict = gpu_web_capacity_verify(over, manifest)
expect(verdict.accepted).to_equal(false)
expect(verdict.first_breach_bound).to_equal("max_host_effects_per_epoch")
expect(verdict.reason).to_equal("gpu_web_capacity_exceeded: max_host_effects_per_epoch requested=5 limit=4 over=1")
```

</details>

#### should bound patch operations at four per draw command

- should bound patch operations at four per draw command
- The patch arena follows the draw-command ceiling it is derived from
   - Expected: manifest.max_patch_operations.to_i64() equals `manifest.max_draw_commands.to_i64() * 4`
   - Expected: manifest.max_patch_operations.to_i64() equals `4096`
- A full patch stream at the derived bound is accepted
   - Expected: gpu_web_capacity_verify(at_bound, manifest).accepted is true
- One operation more than the generator can emit is rejected
   - Expected: verdict.accepted is false
   - Expected: verdict.first_breach_bound equals `max_patch_operations`
   - Expected: verdict.reason equals `gpu_web_capacity_exceeded: max_patch_operations requested=4097 limit=4096 over=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should bound patch operations at four per draw command")
step("The patch arena follows the draw-command ceiling it is derived from")
val manifest = gpu_web_capacity_manifest_compile_time_default()
expect(manifest.max_patch_operations.to_i64()).to_equal(manifest.max_draw_commands.to_i64() * 4)
expect(manifest.max_patch_operations.to_i64()).to_equal(4096)  # oracle: 4096 — named expected value from the requirement
step("A full patch stream at the derived bound is accepted")
var at_bound = gpu_web_capacity_plan_zero()
at_bound.patch_operations = 4096u32
expect(gpu_web_capacity_verify(at_bound, manifest).accepted).to_equal(true)
step("One operation more than the generator can emit is rejected")
var over = gpu_web_capacity_plan_zero()
over.patch_operations = 4097u32
val verdict = gpu_web_capacity_verify(over, manifest)
expect(verdict.accepted).to_equal(false)
expect(verdict.first_breach_bound).to_equal("max_patch_operations")
expect(verdict.reason).to_equal("gpu_web_capacity_exceeded: max_patch_operations requested=4097 limit=4096 over=1")
```

</details>

#### should still fail closed on path points, which have no repo-cited bound

- should still fail closed on path points, which have no repo-cited bound
- No constant in the repo bounds path points, so the default leaves it unset
   - Expected: manifest.max_path_points.to_i64() equals `0`
- Asking for a single path point is a loud rejection, not a silent pass
   - Expected: verdict.accepted is false
   - Expected: verdict.first_breach_bound equals `max_path_points`
   - Expected: verdict.reason equals `gpu_web_capacity_exceeded: max_path_points requested=1 limit=0 over=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should still fail closed on path points, which have no repo-cited bound")
step("No constant in the repo bounds path points, so the default leaves it unset")
val manifest = gpu_web_capacity_manifest_compile_time_default()
expect(manifest.max_path_points.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
step("Asking for a single path point is a loud rejection, not a silent pass")
var plan = gpu_web_capacity_plan_zero()
plan.path_points = 1u32
val verdict = gpu_web_capacity_verify(plan, manifest)
expect(verdict.accepted).to_equal(false)
expect(verdict.first_breach_bound).to_equal("max_path_points")
expect(verdict.reason).to_equal("gpu_web_capacity_exceeded: max_path_points requested=1 limit=0 over=1")
```

</details>

#### should keep every uncited bound at zero so nothing is silently permitted

- should keep every uncited bound at zero so nothing is silently permitted
- Walk the bounds this pass found no repo basis for
   - Expected: m.max_css_rules.to_i64() equals `0`
   - Expected: m.max_selectors.to_i64() equals `0`
   - Expected: m.max_selector_candidates.to_i64() equals `0`
   - Expected: m.max_custom_property_edges.to_i64() equals `0`
   - Expected: m.max_layout_boxes.to_i64() equals `0`
   - Expected: m.max_fragments.to_i64() equals `0`
   - Expected: m.max_line_boxes.to_i64() equals `0`
   - Expected: m.max_mutations_per_epoch.to_i64() equals `0`
   - Expected: m.parser_scratch_bytes.to_i64() equals `0`
   - Expected: m.style_scratch_bytes.to_i64() equals `0`
   - Expected: m.layout_scratch_bytes.to_i64() equals `0`
   - Expected: m.scan_scratch_bytes.to_i64() equals `0`
   - Expected: m.backend_preprocess_bytes.to_i64() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should keep every uncited bound at zero so nothing is silently permitted")
step("Walk the bounds this pass found no repo basis for")
val m = gpu_web_capacity_manifest_compile_time_default()
expect(m.max_css_rules.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.max_selectors.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.max_selector_candidates.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.max_custom_property_edges.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.max_layout_boxes.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.max_fragments.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.max_line_boxes.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.max_mutations_per_epoch.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.parser_scratch_bytes.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.style_scratch_bytes.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.layout_scratch_bytes.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.scan_scratch_bytes.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(m.backend_preprocess_bytes.to_i64()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### should pin the frozen contract to a schema version

- should pin the frozen contract to a schema version
- Read the contract version any consumer must agree on
   - Expected: GPU_WEB_CAPACITY_MANIFEST_SCHEMA_VERSION equals `simple-gpu-web-capacity-manifest-v1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should pin the frozen contract to a schema version")
step("Read the contract version any consumer must agree on")
expect(GPU_WEB_CAPACITY_MANIFEST_SCHEMA_VERSION).to_equal("simple-gpu-web-capacity-manifest-v1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b1a7e0c84e663d7dec2219aaf2281d5be46b19b12d88c86500d33fccbe937987`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1a7e0c84e663d7dec2219aaf2281d5be46b19b12d88c86500d33fccbe937987`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1a7e0c84e663d7dec2219aaf2281d5be46b19b12d88c86500d33fccbe937987`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept a plan that fits inside every bound' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept a plan that fits inside every bound' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept a plan that sits exactly at capacity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept a plan that sits exactly at capacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl:75:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject one node over capacity and name the bound' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject one node over capacity and name the bound' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should carry a reason receipt naming bound, request, limit and overflow' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl:101:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report every exceeded bound in frozen contract order' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/ui/gpu_web_capacity_manifest_spec.spl:115:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject rather than silently permit an unset bound' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
