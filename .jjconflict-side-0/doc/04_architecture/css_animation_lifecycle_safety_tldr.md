# CSS Animation Lifecycle Safety — TLDR

Status: **PROPOSED / RED.** Candidate `47df593f600` remains rejected; this is a
docs-only replacement contract with no runtime or PASS claim.

## Core decision

- Identity is
  `BrowserCssAnimationIdentity(document_generation, node_id,
  node_generation, animation_slot, animation_generation)`, never HTML path,
  author `id`, or scalar target state.
- BrowserSession owns bounded lifecycle cursors and the canonical DOM event
  bridge. Draw IR owns pixels only and retains no event/DOM/JS state.
- Ordering uses checked integer ticks and exact decimal iteration counts.
  `f64` conversion occurs only when exposing `AnimationEvent.elapsedTime` to
  JavaScript.
- At most 4,096 live plus 4,096 retiring cursors exist. A fixed queue holds one
  head event per cursor; large clock jumps advance cursors without allocating a
  task for every missed iteration. One host turn dispatches at most 4,096
  events.

## Lifecycle rules

- Cancel the old generation before a same-boundary restart.
- Pause/resume retains generation; finish never later cancels.
- Detach targets the old event handle and is target-only when disconnected;
  replacement at the same path/`id` cannot receive the old event.
- Reinsertion starts a new animation generation.
- Navigation/close clears the destroyed document generation without dispatch
  into its dead JavaScript realm.

## Frozen manual flow

1. `Open the scripted CSS animation lifecycle fixture`
2. `Advance the monotonic clock across exact iteration boundaries`
3. `Cancel and restart the animation through the DOM bridge`
4. `Observe ordered animation events and canonical Draw IR frames`

See
[`css_animation_lifecycle_safety.md`](css_animation_lifecycle_safety.md) and
the
[`agent plan`](../03_plan/agent_tasks/css_animation_lifecycle_safety.md).
