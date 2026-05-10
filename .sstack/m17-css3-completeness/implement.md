# M17 Phase 5 — Multi-Agent Implementation Plan

## Test Baseline (2026-05-10)
| Spec | Status | Notes |
|------|--------|-------|
| css_timing_spec.spl | PASS (22 tests) | Pure math, imports examples.browser.feature.style.animation |
| css_supports_spec.spl | PASS (19 tests) | Imports examples.browser.feature.style.supports |
| css_object_fit_spec.spl | PASS (22 tests) | Pure logic, inline helpers |
| css_sticky_spec.spl | PASS (12 tests) | Pure logic, inline helpers |
| css_custom_properties_spec.spl | PASS (22 tests) | Imports examples.browser.feature.style.custom_properties |
| css_transform_spec.spl | FAIL (13/28) | "cannot convert enum to float" — TransformFunction field access type mismatch |
| css_animation_lifecycle_spec.spl | FAIL (~6/24) | midpoint opacity assertion — value comparison issue in AnimationEngine.tick |
| css_scrollbar_spec.spl | MISSING | Not created in Phase 4 |

## D-1 Resolution: Leave + Canonical Copy

Examples modules stay in `examples/browser/feature/style/` — test specs import from there.
Canonical engine copies the needed logic into `src/lib/.../browser_engine/style/` modules.
No `src/lib/` → `examples/` imports (violates layering). Canonical modules are independent ports.
This matches M13-M16 porting pattern.

## Execution Waves

### Pre-step (Orchestrator — sequential, before agents)
1. Add 6 new StyleProps fields to `css.spl`: transform, transform_origin, transition, animation, object_fit, object_position (all default "")
2. Fix css_transform_spec.spl — patch TransformFunction field access (enum-to-float)
3. Fix css_animation_lifecycle_spec.spl — fix midpoint opacity comparison
4. Create css_scrollbar_spec.spl (AC-5, ~20 tests, pure math)
5. Commit pre-step work

### Wave 1 — New Canonical Modules (3 parallel agents)
All agents create NEW files only in `src/lib/gc_async_mut/gpu/browser_engine/style/`.
No modifications to existing files. No commits. No jj.

**Agent A — Animation Engine**
- Files: `style/animation.spl`, `style/animation_controller.spl`
- Port from: `examples/browser/feature/style/animation.spl`, `animation_controller.spl`
- Content: AnimationEngine, Animation, Transition, Keyframe, AnimationState, FillMode, PlayDirection, TimingFunction, StyleUpdate, ease_value, cubic_bezier, interpolate_length, interpolate_keyframes, AnimationController, ActiveTransition, is_transitionable, tick()
- Adapt: use canonical imports (std.gc_async_mut.gpu.browser_engine.css for StyleProps)
- Verify: module compiles standalone

**Agent B — Transform + Custom Properties**
- Files: `style/transform.spl`, `style/custom_properties.spl`
- Port from: `examples/browser/feature/style/transform.spl`, `custom_properties.spl`
- Content: parse_transform, compose_transform, TransformFunction, Matrix4, matrix4_identity, matrix4_multiply; CustomPropertyStore, set_property, resolve_var, resolve_all_vars, register_property, is_custom_property, has_var_reference, parse_var_function
- Adapt: self-contained, no engine imports needed (leaf modules)
- Verify: module compiles standalone

**Agent C — Supports + RenderState**
- Files: `style/supports.spl`, `style/render_state.spl`
- Port from: `examples/browser/feature/style/supports.spl` (supports); architecture spec (render_state)
- Content: eval_supports_query, known_properties (supports); RenderState class with anim_controller, custom_props, scroll_offsets map, computed_transforms map, keyframe_registry map, render_state_new(), render_state_clear() (render_state)
- Verify: module compiles standalone

**Post-Wave-1**: Orchestrator commits Wave 1 output.

### Wave 2 — Wire Existing Engine Files (3 parallel agents)
Each agent owns disjoint files. No commits. No jj.

**Agent D — DOM Wiring**
- Files owned: `dom.spl`
- Task: Add set_style() dispatch arms for: "transform" → s.transform, "transform-origin" → s.transform_origin, "transition" → s.transition, "animation" → s.animation, "object-fit" → s.object_fit, "object-position" → s.object_position
- Also: wire custom property detection (if prop starts with "--", store in custom props via function call)
- Import: style/custom_properties for is_custom_property()

**Agent E — Style-Block Wiring**
- Files owned: `style_block.spl`
- Task: (1) @keyframes block extraction — detect `@keyframes name { ... }` in CSS text, parse into keyframe data, return alongside rules; (2) @supports block evaluation — detect `@supports (prop: val) { ... }`, evaluate with eval_supports_query(), include/discard contained rules; (3) @property registration — detect `@property --name { ... }`, call register_property(); (4) var() resolution — integrate CustomPropertyStore.resolve_var() into existing resolve_css_vars_in_value()
- Import: style/supports, style/custom_properties

**Agent F — Layout + Paint**
- Files owned: `layout.spl`, `paint.spl`
- layout.spl tasks: (1) Add scroll_offset_y, scroll_offset_x fields to BeLayoutBox or pass as params; (2) Post-layout sticky clamping pass — after normal flow, iterate position:sticky boxes, clamp to scroll container edges using top/bottom/left/right insets; (3) Thread scroll offset for overflow:scroll containers
- paint.spl tasks: (1) Transform matrix — before painting a node with non-empty transform, compute Matrix4 via compose_transform(), apply translate offset to PaintCmd coordinates; (2) Scrollbar rendering — for overflow:auto/scroll nodes where content overflows, emit track+thumb PaintCmd::Rect pairs (SCROLLBAR_WIDTH=15); (3) Scroll clipping — clip child paint commands to scroll container bounds; (4) object-fit in image arm — apply cover/contain/fill/none/scale-down logic from object_fit_size() helper
- Import: style/transform (paint.spl only)

**Post-Wave-2**: Orchestrator commits Wave 2 output.

### Wave 3 — Browser Renderer Integration (Orchestrator — sequential)
- File: `browser_renderer.spl`
- Tasks: (1) Create RenderState instance, store on BrowserRenderer; (2) Call AnimationController.tick(now_ms) in render_dom() loop; (3) Apply StyleUpdate results back to nodes; (4) Replace br_resolve_css_var() with CustomPropertyStore lookups; (5) Thread keyframe_registry from style_block @keyframes extraction; (6) Thread scroll_offset from RenderState into layout calls
- Run: all 8 specs, 132-corpus regression gate

## Agent Rules
- **DO NOT** commit, run jj, or git add — orchestrator handles VCS
- **DO NOT** modify files outside your assigned scope
- Each agent has `advisor()` access — call it before committing to an approach
- Use `bin/simple test <spec>` to verify changes where applicable
- Follow Simple language rules: no inheritance, composition/traits, `me` receiver, `val`/`var`, generics `<>`
