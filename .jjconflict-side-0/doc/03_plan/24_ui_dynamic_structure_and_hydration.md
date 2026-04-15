# Plan 24: UI Dynamic Structure, Keyed Diffing, and SSR/Hydration

## Goals
- Implement the “very difficult” parts from `doc/ui.md`: dynamic child structure (`if/for` in render blocks with keyed nodes) and server-side rendering with hydration.
- Keep GUI (HTML) and TUI renderers aligned by sharing TemplateIR, node IDs, and PatchSet semantics.

## Scope
- Render-time control blocks: `<% if %>`, `<% for %>`, keyed lists (`key=` attribute) inside `.sui`.
- PatchSet extensions for structural changes: insert/remove/replace child, keyed reconciliation.
- Renderer updates (GUI/TUI) to apply structural patches and maintain focus/ordering.
- SSR path: render to HTML string + hydration metadata, then hydrate on the client by reusing existing DOM/tree.

## Dependencies and Reuse
- Reuse existing UI parsing and IR split: InitIR (instantiate), TemplateIR (static tree), RenderIR/Wasm (render stage).
- Node ID policy from current static template support; extend with stable IDs for keyed lists.
- Binding graph/invalidation from milestone 2; extend to track dynamic child sets.
- PatchSet type lives in UI runtime crate; extend rather than fork per backend.

## Workplan
1) Grammar and IR upgrades (render stage)
   - Add AST/IR nodes for `IfNode`, `ForNode`, and keyed attributes on elements.
   - Extend TemplateIR with `DynamicBlock` markers referencing render-time control nodes.
   - Emit RenderIR/Wasm stubs for the new control nodes: runtime helpers to push/pop child scopes, evaluate conditions, iterate, and emit keyed child descriptors.

2) PatchSet semantics for structure
   - Add ops: `InsertChild(parent_id, index, Subtree)`, `RemoveChild(parent_id, child_id)`, `ReplaceSubtree(node_id, Subtree)`, `MoveChild(parent_id, from, to)` (optional if keyed).
   - Define `Subtree` encoding (node type, attrs, children, hole bindings) reusable by GUI/TUI.
   - Document ordering rules: keyed diff preserves key order; unkeyed uses index order only.

3) Diff and keyed reconciliation
   - Implement a render-time diff helper that compares previous rendered snapshot vs new emission from RenderWasm:
     - Keyed lists: map keys → old child; emit moves/inserts/removals accordingly.
     - Unkeyed lists: simple truncate/append with index-based replace.
   - Ensure stable `ui_counter` increment semantics for generated children to keep selector/id compatibility.

4) Renderer integration (GUI + TUI)
   - GUI: map structural PatchSet ops to DOM insert/remove/replace; ensure event/binding reattachment is driven by binding graph (no dangling listeners).
   - TUI: update screen tree and focus order; ensure scroll containers recompute layout after structural changes.
   - Shared: when nodes are removed, detach bindings and free associated state handles.

5) SSR + Hydration
   - Server render: run InitIR + RenderWasm to produce HTML string and hydration manifest (node IDs, key paths, hole bindings, event wiring hints).
   - Client hydrate: attach to existing DOM/tree, rebuild binding graph, and initialize wasm instance without rerendering; on mismatch, fallback to full rerender.
   - Align hydration manifest with PatchSet so later updates reuse the same node IDs.

6) Testing and validation
   - Unit: keyed diff cases (insert/move/remove), unkeyed behavior, PatchSet serialization.
   - Integration: GUI DOM smoke tests (add/remove rows), TUI focus order stability after list updates.
   - SSR: roundtrip render+hydrate+update test to ensure no double-render and events work.
   - Performance checks: keyed diff O(n) behavior, no quadratic loops on large lists.

## Risks and Mitigations
- **ID/selector instability**: lock down node ID generation rules and share between GUI/TUI; add assertions in tests.
- **Hydration mismatch**: provide clear fallback path and logging; gate hydration on manifest version.
- **Event leaks**: ensure renderer removes listeners/bindings on node removal.

## Out of Scope (later)
- Streaming/partial hydration, advanced diff optimizations (e.g., LIS move detection), full CSS parity in TUI.
