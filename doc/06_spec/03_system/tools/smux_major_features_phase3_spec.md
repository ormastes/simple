# SMUX split orientation through client refresh

**TEST_BLOCKED — authored manual. Native compilation, execution and SPipe docgen
are pending; no execution PASS or zero-stub result is claimed.**

Executable: [smux_major_features_phase3_spec.spl](../../../../test/03_system/tools/smux_major_features_phase3_spec.spl).
Plan: [SMUX Phase 3 suite](../../../03_plan/sys_test/smux_major_features_phase3.md).
Baseline: `release/1.0.0` at `1e431722b40236eda5e80bd5f5bf06395b0d0d08`.

This regression checks actual SMUX decoder, service and interactive protocol
state. It starts no shell and uses no test service implementation. Terminal key
delivery, TCP transport, ConPTY background progress and independent client screens
retain separate native fixtures. A protocol frame header is not a host screenshot.

## Keep a horizontal split when the client refreshes

Requirements: REQ-SMUX-CORE-002, REQ-SMUX-INTERACTIVE-001/003.

1. Create an 80 by 24 production window. Decode Ctrl-B and quote in separate
   chunks, requiring the `split-horizontal` action.
2. Apply the decoded direction through the production split API. Require 11
   upper rows and 12 lower rows, separated by one row.
3. Request `client-layout ... current 80 24`, then capture two real protocol
   frames with different cursor panes.
4. Require the original and new pane IDs at `(0,0,80,11)` and `(0,12,80,12)`.
   Both frames must retain an 80 by 24 canvas.

The old tiled fallback produces columns and therefore fails the rectangle oracle.
Source reasoning identifies that failure; no baseline execution is claimed.

## Change orientation only when a named layout is selected

Requirements: REQ-SMUX-CORE-002/005, REQ-SMUX-INTERACTIVE-001.

1. Decode Ctrl-B percent and split the production window vertically.
2. Request a frame before an arrange request. Require left `(0,0,39,24)` and
   right `(40,0,40,24)` rectangles with the actual pane IDs.
3. Explicitly select `even-vertical` through the interactive dispatcher.
4. Require the same IDs in two full-width named-layout bands:
   `(0,0,80,12)` and `(0,12,80,12)`.

The split separator belongs to manual split geometry. Named-layout bands follow
the existing named-layout contract and fill the canvas without that separator.

## Preserve a nested split across sibling frames and reattachment

Requirements: REQ-SMUX-CORE-001/004, REQ-SMUX-INTERACTIVE-003.

1. Create work and monitoring sessions, then a second logs window in work.
   Focus logs and attach two 80 by 24 clients to work. Attach a smaller client
   to monitoring to check that a foreign session cannot shrink work.
2. Split the inactive work window vertically; split only its left pane
   horizontally. Request a sibling frame before arranging.
3. Refuse a split addressed with the monitoring session's pane ID.
4. Detach both work clients, require three retained panes, then reattach at the
   same size. Request the current layout and another frame.
5. Require upper-left `(0,0,39,11)`, untouched right `(40,0,40,24)` and
   lower-left `(0,12,39,12)`, each bound to the actual creation result's ID.
6. Require logs to remain the active window at 40 by 10 and monitoring's pane
   identity/80 by 24 geometry to remain unchanged.

No child exists in this case: detached metadata retention is the claim. Real
background execution remains owned by the existing ConPTY and external-owner
suites. Each scenario resets the real in-process service at setup and completion.

<details>
<summary>Executable SSpec and verification controls</summary>

The canonical executable is the linked `.spl` file above. Its three `it` cases
use modern `step(...)` calls and canonical matchers. Reusable setup is marked
`@inline`; every setup check examines production results. There are no placeholder
passes, shell stand-ins or expected-output files presented as observations.

Root must supply an admitted source-matched Phase 3 CLI, ordered Windows provider
roots and a matching runtime. Run the existing native test route and docgen from
the plan once after the repair. Record actual binary-owned case counts, native
execution, terminal quiescence and docgen's zero-stub result. Until then all three
scenarios remain TEST_BLOCKED.

</details>
