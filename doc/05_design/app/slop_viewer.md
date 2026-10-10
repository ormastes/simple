# Slop viewer design

Status: target design; implementation pending. Authority: report sections 16–17.

Left pane is a keyboard-operable MDSOC tree/search. Upper right is a stable
left-to-right feature → requirement → acceptance → lower-level test →
implementation graph with supporting artifacts folded. Lower right inspects
canonical identity, attributes, origins, relations, evidence and revision-pinned
source. Footer names snapshot, current/last-valid generation, scope and diagnostics.

Selection in any dimension selects the same canonical node. Focus and selection
are separate; refresh preserves focus and expanded groups where IDs remain.
Arrow keys navigate trees, pane navigation and source links work without a mouse,
and a nonvisual relation list exposes the graph. Visible limits expose hidden
counts; filtering cannot change qualification. Source/layout work is cancellable
and asynchronous. Useful initial neighborhood is at most 200 visible nodes;
loaded selection target is 150 ms.

Service and viewer consume `TraceProjection`; neither infers edges or evidence
eligibility. SDN message generations/deltas bind exact base/new snapshot IDs.
Lost/mismatched delta requires complete resync. Invalid current inputs retain a
conspicuously last-valid view with diagnostics and no current green badge.
Historical evidence navigates to historical source bytes, never moving worktree.

Read-only service has session/origin checks and explicit capability boundaries.
IDs resolve through admitted source locators and visibility policy, never arbitrary
filesystem paths. Repository source/Markdown is escaped inert display content.
Offline HTML pre-renders navigation or embeds escaped SDN text; no JSON data islands
or executable object literals. Export remains governed by visibility and explicit
publication authorization. Architecture/design/dependency views reuse identities.

Acceptance: AC-TRC-032–037/040 and applicable projection/eligibility cases.
No frontend/server is deployed by this document.
