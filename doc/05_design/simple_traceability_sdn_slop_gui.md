# Slop viewer GUI and TUI interaction design

Date: 2026-10-03. Status: proposed native MVP; runtime acceptance pending.
Companion: `app/slop_viewer.md` inventories actual APIs and gaps.

## Workspace

The default native window has a resizable left tree (22% width), upper-right
layered graph and lower-right inspector (60/40 height). A status bar always
shows snapshot identity, candidate/committed/historical mode, graph generation,
scope completeness and diagnostic count. User-local SDN stores dimensions.

```text
+-----------------------+--------------------------------------------------+
| Search ID/title/path  | Feature | Requirement | AC/tests | Tests | Impl    |
| View by: Feature     | Actual labeled typed edges; hidden-group counts   |
| > Compiler           | Selected node; forward trace / reverse impact     |
|   > Parser           | Showing 200 / 4300; expand or next page            |
| > Shared components  +--------------------------------------------------+
| > Unassigned         | Identity | Relations | Evidence | Source | Docs   |
| > Unresolved         | Snapshot / run / provenance / eligibility reason |
|                      | Revision-pinned content with line numbers        |
+-----------------------+--------------------------------------------------+
| Snapshot: ... | Graph: valid/stale | Scope: complete/partial | Issues ... |
+-------------------------------------------------------------------------+
```

This layout is a design sketch, not implementation evidence. The delivered
view must use the native Simple UI session and respond to real events.

## Selection and navigation

Tree grouping offers feature, layer, component/entity, transform, requirement,
test and source dimensions. Repeated aliases share canonical selection but
retain independent expansion. Search matches IDs, titles, symbols and paths;
each result shows its match reason and revision context. The inspector retains
the selected ID across a regroup when still present; otherwise it shows an
explicit unavailable-selection state rather than choosing the first match.

The graph offers forward trace, reverse impact, requirement, test,
implementation and provenance actions. Trace phases are stable left to right;
architecture layers are a separate grouping, not permission to import across
layers. Shared components retain all actual relations. Folded support documents
show counts. Every inferred edge exposes its convention and rule version.

The Evidence tab displays test definitions separately from actual executions.
An acceptance pass next to an unexecuted unit test reads `pass` and `not_run`.
Stale and rejected observations retain their reasons and original run identity.
No completion percentage overrides this detail. Source opens lazily with
snapshot, path/blob identity and lines in its header. Switching snapshots
clears pending old source; unavailable content is visibly unavailable.

## Keyboard, accessibility and smaller screens

Tab/Shift-Tab traverse panes and controls. Up/Down move tree focus, Right opens
a branch or enters its first child, Left collapses or moves to its parent,
Home/End select the first/last visible focus target, Enter activates selection,
Escape exits temporary navigation. Focus is visible and separate from selected
state. Graph nodes are reachable through the equivalent typed relation list;
all statuses have text and icons, not color alone. Announce changed selection,
loading/error state and bounded-result count using semantic UI properties.

At narrow widths, tree/graph/inspector become explicit tabs over the same
session and selected ID. TUI uses an expandable tree, stable phase-grouped
adjacency list with edge labels, inspector text and exact snapshot/status bar.
TUI evidence semantics and source pinning are identical; terminal adaptation
does not claim a graphical canvas was tested.

## Required visual-state cases

Capture normal selection, shared implementation reverse impact, unresolved
mapping, partial graph/pagination, mixed evidence outcomes, historical source,
missing blob, invalid live delta and keyboard focus. Native interaction tests
assert selection and inspector changes in typed access snapshots as well as
images. Record the host/provider used and link captures in generated manuals.
Pending runtime/provider support is an incomplete criterion, not a substitute
static page or fabricated screenshot.
