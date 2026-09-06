# WM Glass Theme on Host and SimpleOS — Requirements

## Selected Direction

Feature Option A: use the registered `aetheric_dark` package as the single
Stitch-derived theme authority across hosted WM, Simple GUI, Simple Web, and
canonical SimpleOS/QEMU. Legacy theme names may resolve as aliases, but no
renderer may maintain a competing hard-coded Aqua or legacy color branch.

## Functional Requirements

- **REQ-001 — Single authority:** `config/themes/theme.sdn` and the resolved
  `aetheric_dark` package determine the production theme identity and revision.
- **REQ-002 — Typed glass semantics:** resolution exposes desktop/window/title
  fills, alpha, blur/saturation, border, radius, layered shadow, typography,
  foreground/secondary text, active/inactive state, and accessibility fallback.
- **REQ-003 — WM and Simple GUI wiring:** production WM chrome and widget
  lowering consume the resolved semantic theme; test-only adapters and
  hard-coded defaults are insufficient.
- **REQ-004 — Simple Web CSS wiring:** hosted Web content consumes the resolved
  package CSS rather than a renderer-owned color fragment.
- **REQ-005 — CSS preservation:** supported RGBA, variables, gradients,
  borders/radii, layered box shadows, backdrop blur/saturation, typography, and
  active/inactive selectors survive parse, cascade, computed style, semantic
  accessors, and Draw IR lowering.
- **REQ-006 — Canonical hosted route:** themed production frames travel through
  `SharedWmScene -> DrawIrComposition -> Engine2D`; evidence declares whether
  fallback occurred.
- **REQ-007 — Canonical SimpleOS route:** x86_64
  `gui_entry_desktop.spl` and `engine2d_wm_frame_executor.spl` use the same
  resolved theme fingerprint; legacy `wm_entry.spl` cannot satisfy this gate.
- **REQ-008 — Interaction integrity:** focus, pointer down/up, move/maximize,
  keyboard/text input, animation timing, and active/inactive visual state remain
  functional after theme wiring.
- **REQ-009 — Accessibility policy:** reduced-transparency/unsupported-blur
  paths use an explicit solid material fallback with readable contrast and
  report that fallback in evidence.
- **REQ-010 — Root-cause ownership:** discovered gaps are fixed in the theme,
  CSS/computed-style, semantic accessor, Draw IR, or canonical WM owner; no
  fixture bypass, private renderer, raw-runtime shortcut, or synthetic frame is
  accepted.

## Traceability Target

Each REQ must map to an executable SPipe scenario, focused implementation test,
or retained host/QEMU evidence check. Screenshots without structured semantics
and provenance do not establish completion.
