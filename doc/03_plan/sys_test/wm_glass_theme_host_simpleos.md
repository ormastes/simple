# System Test Plan: WM Glass Theme on Host and SimpleOS

## Primary Spec

Executable:
`test/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.spl`

Manual:
`doc/06_spec/03_system/app/simple_wm/feature/wm_glass_theme_host_simpleos_spec.md`

## Scenarios

1. Canonical happy path: resolve `aetheric_dark`, assert complete material,
   render host and QEMU through canonical routes, compare semantics and pixels.
2. Interaction: focus swap, pointer drag, maximize/restore, keyboard/text and
   animation frames change semantic and pixel state coherently.
3. CSS matrix: variables, RGBA, gradient, border/radius, layered shadow,
   backdrop blur/saturation, typography and state selectors survive every stage.
4. Accessibility: reduced transparency and unavailable blur choose the named
   solid fallback with readable contrast.
5. Fail closed: corrupt hash, unknown capability, stale capture, legacy QEMU
   entry and forced direct renderer are rejected.
6. Determinism/performance/provenance: hashes and region policies repeat;
   startup/frame/QEMU/RSS metrics and complete identities are retained.
7. Ownership: no fixture, private renderer, raw-runtime or synthetic route.

## Manual Flow

Use these exact visible steps:

1. `Load the Stitch glass theme`
2. `Render the hosted WM through the canonical scene`
3. `Apply glass CSS and widget computed styles`
4. `Boot the canonical SimpleOS desktop in QEMU`
5. `Capture and compare semantic and framebuffer evidence`

Setup helpers are `@inline`; secondary/error/matrix scenarios are folded and
use `@prev` only for already-created evidence. Capture kinds are protocol,
HTML, GUI, binary, log and artifact. The generated manual uses linked evidence.

## Requirement Trace

| Requirement | Scenarios |
|---|---|
| REQ-001 | 1, 5, 6 |
| REQ-002 | 1, 3, 4 |
| REQ-003 | 1, 2, 7 |
| REQ-004 | 1, 3, 7 |
| REQ-005 | 1, 3, 5 |
| REQ-006 | 1, 5, 7 |
| REQ-007 | 1, 5, 7 |
| REQ-008 | 1, 2, 5 |
| REQ-009 | 1, 4, 5 |
| REQ-010 | 1, 5, 7 |
| NFR-001..008 | 1, 4, 5, 6, 7 |

## Focused Regression Specs

Extend theme-package, WM-chrome, Simple-Web-window, Web glass-feature-gap,
Engine2D glass, canonical GUI-entry contract and QEMU evidence-contract specs.
Each test uses built-in matchers and concrete values. Missing runtime helpers
must call `fail("wm glass theme evidence not implemented")` until implemented.
