<!-- codex-research -->
# UI Access Protocol — Domain Research

**Date:** 2026-04-15
**Feature:** `ui_access_protocol`
**Status:** Applied to internal-only v1 design

## Summary

External research supports the same direction the project plan already reached:

- accessibility-tree style semantics are the best model for LLM-facing UI
  interaction
- window-manager metadata should stay a separate top-level inventory
- screenshots and marks are a fallback, not the primary v1 protocol
- declarative or snapshot-oriented interfaces are better LLM inputs than raw
  imperative click streams

For this repository, those ideas map onto the internal Simple UI tree rather
than native OS accessibility in v1.

## Relevant External Patterns

### Accessibility tree as the semantic base

- Windows UI Automation models the desktop as a root tree with semantic control
  patterns and element properties.
- Browser tooling like Playwright ARIA snapshots and Chrome CDP accessibility
  trees show that compact semantic tree rendering is both practical and
  LLM-friendly.

Project implication:

- model Simple UI surfaces as semantic trees with stable node references
- expose surface inventory separately from node inventory

### Window graph as supporting metadata

- WM APIs are useful for title, focus, ownership, z-order, and bounds
- they are not enough for control-level automation

Project implication:

- keep `window_id`/title metadata on surfaces
- do not try to make WM APIs the primary control model

### Hybrid semantic + history + vision architecture

- OSWorld, SoM, and similar work show that semantic trees plus visual fallback
  are practical in production
- vision-only approaches are universal but less reliable for exact controls

Project implication:

- v1 should stop at semantic tree + recent history
- future v2 can add screenshot/mark fallback on top of the same canonical IDs

### Declarative LLM-facing interface

- recent GUI-agent work argues that an LLM-facing state/observe/access layer
  reduces interaction cost and improves reliability compared with low-level
  click scripting

Project implication:

- the protocol should center on `snapshot`, `surface`, `find`, `act`, and
  `history`
- text/markdown rendering should be derived from the canonical snapshot, not
  handwritten tool-specific formatting

## Why External Accessibility Is Not v1

Even though native accessibility trees are strong prior art, they do not fit
the immediate repo need:

1. The repo already owns its own semantic UI tree for shared surfaces.
2. The internal UI test API and MCP tooling already operate on that tree.
3. External UIA/AT-SPI/AX integration would broaden scope into cross-process,
   platform-specific discovery before the internal contract is stable.

So the correct v1 use of this research is structural:

- follow accessibility-tree ideas
- implement them over the internal Simple UI runtime

## Applied Domain Conclusions

- canonical node IDs should be stable and human-inspectable
- event/history capture should be incremental and bounded
- snapshot fetches should be cheap and derived from current session state
- tools and skills should share one protocol vocabulary
- future external adapters should target the same snapshot shape rather than
  inventing a second one
