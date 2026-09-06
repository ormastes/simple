# WM Full-Stack Demo Requirements

Selected by the user on 2026-07-29: **Linux/GLFW Phases 0–6 plus isolated
compiler regressions**.

## Functional Requirements

- REQ-001: Provide one canonical pollable window-event contract with a bounded
  queue, generation-counted handles, independent modifiers, separate key and
  committed-text events, overflow accounting, and explicit capability errors.
- REQ-002: Provide a deterministic headless implementation and a real Linux
  GLFW adapter without creating a second compositor or renderer.
- REQ-003: Preserve logical size, framebuffer pixel size, and content scale as
  separate values; stage/present ARGB pixels at framebuffer dimensions.
- REQ-004: Replace opaque or universal-Web production content dispatch with
  explicit GUI, Simple Web, and pixel producer identity.
- REQ-005: Every producer must enter the compositor as a validated
  `WmContentFrame`; GUI and nested content must use the existing shared checksum,
  revision, parent, and offset contract.
- REQ-006: Retain a real `UISession`; route normalized pointer, wheel, key,
  committed text, focus, and clipboard commands into it; render changed session
  state through widget Draw IR and Engine2D.
- REQ-007: The demo client must visibly contain one VBox with static text, an
  image, editable text field/caret, button, scroll view/scrollbar, nested Simple
  2D surface, nested Simple Web panel, and latest-event status.
- REQ-008: `RenderSurface` must clip child pixels, translate pointer coordinates,
  forward focus/capture, and emit parent-relative nested content frames.
- REQ-009: The live scenario must prove button activation, text entry,
  Ctrl+A/C/V and one app shortcut, nested 2D dragging, wheel/thumb scrolling,
  and titlebar dragging through normalized input.
- REQ-010: Window lifecycle must use Normal, Minimized, Maximized, Closing, and
  Closed semantics. Collapse is an alias for minimize. Maximize/restore must
  preserve the exact prior normal geometry.
- REQ-011: Pin/unpin must operate on stable `app_id` values, preserve ordering,
  survive window close/reopen within the desktop service, and remain separate
  from running `window_id` entries.
- REQ-012: Closing a window must cancel pointer capture, release GUI/Web/pixel
  content, remove the running taskbar item, and return window, event, content,
  and pixel handle counts to baseline.
- REQ-013: The GLFW lane must retain runtime evidence: backend identity, native
  input receipts, frame and content revisions, semantic state, screenshot or
  framebuffer pixels, stable region checks, and handle counts.
- REQ-014: Unsupported operations must return an explicit unsupported/capability
  status. No wrapper may fabricate success.
- REQ-015: Add isolated native regressions for concrete-to-trait dispatch,
  aggregate by-value/module-global/Option/Result/array/nested-return behavior,
  entry-closure unresolved stubs, and strong-over-weak symbol selection.
- REQ-016: Reuse the existing lifecycle, taskbar, `WmContentFrame`, widget Draw
  IR, `UISession`, Engine2D, and hosted compositor owners; do not fork equivalent
  state machines or rendering paths.

## Deferred Contract Consumers

The following remain required product lanes but are outside this first
implementation acceptance:

- SDL3 and repaired SDL2 window adapters.
- Real miniaudio, SDL3, and SDL2 PCM device backends.
- QEMU SimpleOS visual/input parity and HDA DMA/IRQ activity.
- Native UNO Q SimpleOS on QRB2210/AArch64.

They must reuse REQ-001 through REQ-016 and require their own fresh runtime
evidence before completion.

## Acceptance

The first slice passes only when the same executable scenario succeeds through
the headless contract and a real Linux GLFW window, and the compiler regressions
run through their intended native gates. Source inspection is not runtime
acceptance.
