Simple UI Library Specification

JSP-like UI files, paired UI/Logic directories, dual-stage execution (instantiate vs render/update), dual renderer (HTML GUI + TUI simulation)


---

1. Goals and non-goals

Goals

One UI definition runs in:

GUI: real HTML/CSS (browser / webview / future web target)

TUI: simulated layout + styling (tuicss-like) with keyboard/focus navigation


JSP-like authoring: UI files are “HTML-first” with embedded Simple code.

Two execution stages in one UI file:

Instantiation-time (run once per instance; build bindings, init state, register events)

Render/update-time (compiled to WASM; run per update; produces patch-set)


File/class matching: each UI file has a matching Simple class in a paired logic directory.


Non-goals (initially)

Full CSS implementation in TUI (map a subset only).

Full browser DOM API access from WASM (render uses patch-set, not direct DOM ops).

Complex diff engine on day one (start with “hole patching”, then evolve).



---

2. Repository layout: UI + Logic pairing

A strict convention removes ambiguity and enables tooling (compiler, watcher, IDE) to find logic from UI and vice versa.

Recommended layout

app/
  ui/
    pages/
      Home.page.sui
      Settings.page.sui
    components/
      Counter.ui.sui
      Dialog.ui.sui
    layouts/
      AppShell.ui.sui
  logic/
    pages/
      Home.spl
      Settings.spl
    components/
      Counter.spl
      Dialog.spl
    layouts/
      AppShell.spl

  assets/
    styles/
      base.css          # GUI only
      theme.tui.json    # TUI mapping

Matching rules (hard requirement)

For a UI file:

app/ui/components/Counter.ui.sui


The logic file must exist:

app/logic/components/Counter.spl


And contain a matching public class:

class Counter { ... }


Same for pages:

Home.page.sui ↔ Home.spl containing class Home.


Why this matters

Deterministic linking in the compiler.

Predictable hot-reload and dependency tracking.

Enables “open counterpart” editor commands (like you do with header/cpp).



---

3. UI file types: root vs embedded

Root page UI

Extension: *.page.sui

Must define a single root (document/window/mount root).

Owns routing/mount policy, page-level context and session usage.


Embedded component UI

Extension: *.ui.sui

Defines a reusable component template used inside pages/other components.

May declare props, events, slots.


Both compile into the same internal artifacts; the only difference is: root page has a mount root and a page lifecycle.


---

4. JSP-like syntax with two-stage blocks

You requested:

“2 stage variable and statement”

“instanciate time and rendering update time”

“rendering time statement code compiled wasm”


Block taxonomy

Stage A: Instantiation-time (host runtime, once)

Use blocks that are explicitly “setup-time”:

<%@ ... %> directives (compile-time + instantiate config)

<%! ... %> declarations (instance fields, helper methods, static defs)

<%~ ... %> instantiate statements (executed once per component instance)


Stage B: Render/update-time (compiled to WASM, many times)

<%= expr %> render expression “hole”

<% code %> render statements (if/for/let), compiled to WASM


Example: component UI file

app/ui/components/Counter.ui.sui

<%@ component name="Counter" %>

<%! 
  # instance fields (exist across renders)
  let count: i32
%>

<%~ 
  # instantiate-time init (run once)
  this.count = props.start
  bind(this.count, "#countText")     # build dependency graph
  on_click("#incBtn", this.increment)
%>

<Box>
  <Text id="countText">Count: <%= this.count %></Text>
  <Button id="incBtn">Inc</Button>
</Box>

Matching logic file: app/logic/components/Counter.spl

class Counter {
  fn increment() {
    this.count += 1
    invalidate()  # request re-render (or auto from binding)
  }
}

Notes:

bind() and on_click() are instantiate-time runtime APIs.

<%= this.count %> is a render-time expression compiled into WASM.



---

5. Runtime model: component instance, context, session

Each instantiated UI has:

props: immutable inputs (for a given instance; can update via parent)

state: fields declared via <%! ... %> / logic class fields

context: hierarchical dependency injection (theme, locale, shared services)

session: user/session-scoped storage (client app: persistent store; web: HTTP session analog)

ui_counter: per-element instance counters (stable IDs for lists, keyed rendering)


Core objects

UiInstance

ComponentInstance

RenderContext { props, this, context, session }

BindingGraph (state → affected holes/nodes)

PatchSet (output of render-time WASM)



---

6. Rendering architecture (GUI HTML vs TUI)

Compiler output (per UI file)

InitIR (instantiate-time program)

TemplateIR (static node tree with dynamic holes)

RenderWasm (WASM module/function that returns PatchSet)


Runtime phases

1. Instantiate

Execute InitIR on host runtime

Create BindingGraph + event wiring



2. Initial render

Call RenderWasm(render_ctx) → PatchSet

Backend applies PatchSet to:

HTML DOM (GUI)

Terminal buffer (TUI)




3. Update loop

Events mutate state (logic methods)

BindingGraph determines what is dirty

Call RenderWasm() again

Apply PatchSet diff




Backend abstraction

RendererBackend.apply(patch: PatchSet)

GUI backend translates to DOM operations and CSS classes.

TUI backend translates to screen buffer operations, focus/keyboard navigation.



---

7. UI library public API (minimal v1)

Instantiate-time APIs (host runtime)

bind(field_ref, selector_or_hole_id)

invalidate() / schedule_render()

on_click(selector, handler)

on_key(selector, key, handler)

provide(key, value) / use(key) for context

session_get(key) / session_set(key, value)

mount(root_selector) (pages only)

navigate(route) (pages only)


Render-time APIs (WASM-safe)

Pure helpers: formatting, escaping, i18n lookup, class merging

Conditional and loops in <% %> blocks

No direct DOM/terminal access; only “emit patch ops”



---

8. Feature list (by milestone) with development plan

Milestone 0 — Tooling skeleton (low–medium)

Parser for .sui (HTML-like + code blocks)

Split into InitIR/RenderIR/TemplateIR

Pairing rule enforcement (UI ↔ Logic file/class)

Basic build pipeline: sui -> wasm + metadata


Difficulty: Medium (parser + IR design, but constrained scope)


---

Milestone 1 — Static template + text holes (medium)

Support <%= expr %> in text and attributes

No structural diffs yet (no dynamic child list)

PatchSet supports:

SetText(nodeId, text)

SetAttr(nodeId, name, value)

AddClass/RemoveClass



Difficulty: Medium (stable node IDs + hole mapping)


---

Milestone 2 — Events + reactivity core (high)

Instantiate-time binding graph:

track which fields affect which holes


Event system:

GUI: DOM events → dispatch → logic method

TUI: keyboard navigation + “activate” semantics


Update scheduling / batching (microtask-like for GUI, tick loop for TUI)


Difficulty: High (correctness, edge cases, avoiding infinite loops)


---

Milestone 3 — TUI renderer (high)

Layout engine subset:

vertical/horizontal stack

width/height constraints

padding/margin subset


Theme mapping (CSS-ish → terminal style)

Focus, tab order, scrolling containers


Difficulty: High (layout + input model are non-trivial)


---

Milestone 4 — Dynamic structure (very high)

<% if %>, <% for %> generating child lists

Keyed lists (key= attribute) for stable identity

PatchSet extends:

InsertChild(parentId, index, subtree)

RemoveChild(parentId, childId)

ReplaceSubtree(nodeId, subtree)



Difficulty: Very High (diffing, stable identity, performance)


---

Milestone 5 — Server-side rendering + hydration (very high)

Server render to HTML string (or DOM-less tree)

Hydration: bind WASM runtime to existing DOM

Session semantics align with web


Difficulty: Very High (hydration correctness, mismatch handling)


---

9. Difficulty/risk matrix (summary)

Area    Difficulty  Key risks

UI/logic pairing + build tooling    Medium  naming edge cases, refactors
Template parsing + IR   Medium–High HTML+code grammar, error recovery
WASM render function    High    ABI design for PatchSet, perf
Reactivity/binding graph    High    dependency tracking, invalidation correctness
TUI renderer + layout   High    layout rules, input/focus, terminal quirks
Structural diffs (lists/conditionals)   Very High   stable keys, patch complexity
SSR + hydration Very High   DOM mismatch, partial hydration, security



---

10. Recommended “v1” scope (to ship something usable)

If you want an early working system for your client GUI/TUI app:

Milestone 0–3 only

Constrain templates to:

static structure

dynamic text/attrs

events

no dynamic child lists (initially) This yields a usable app framework quickly, and you can add lists/diff later.




---

If you want, I can convert the above into a repository-ready markdown spec (e.g., doc/spec/ui_framework.md) and add:

precise grammar for .sui

exact PatchSet ABI (binary layout / serialization)

a concrete minimal component set (Box, Text, Button, Input, List, Window)

the rules for node IDs and selectors so TUI and GUI stay consistent.
