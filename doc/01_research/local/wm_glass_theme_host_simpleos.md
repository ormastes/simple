# WM Glass Theme on Host and SimpleOS — Local Research

## Scope

Trace the selected theme from configuration through hosted WM, Simple GUI,
Simple Web, Draw IR, Engine2D, and the canonical SimpleOS/QEMU desktop.

## Authoritative Findings

- `config/themes/theme.sdn` selects `aetheric_dark` and aliases every legacy
  `glass_*` name to it. Its package points to `config/themes/aetheric_dark/base.css`.
- Commit `2248995c72` (`feat(wm): Aqua Mac-glass theme`) changed WM defaults to
  hard-coded Aqua values without changing the theme registry. The product now
  has two competing theme authorities.
- `src/os/compositor/simple_web_window_renderer.spl` defaults to
  `aetheric_dark`, but emits a small hard-coded CSS fragment and branches only
  for legacy light IDs. It does not load the resolved package CSS.
- `apply_simple_theme_to_wm_chrome` has test callers but no production caller.
  WM chrome therefore does not consume the resolved theme package.
- WM CSS color conversion accepts only opaque hex forms. The authoritative
  package uses `rgba(...)`, so translucent colors fall back silently.
- the HTML/WebIR-to-DrawIR path drops backdrop-filter projection and reduces
  shadow fidelity. `dom_accessors.spl` reports empty box shadows, zero backdrop
  blur, and no gradient despite lower layers having partial support.
- `theme_registry()` constructs a fresh empty registry per call; registrations
  are not demonstrably retained across callers and need an executable test.
- `src/app/cli/theme_sync.spl` labels both generated constants and live WM
  switching as incomplete; current generated output is hard-coded.

## Runtime Paths

Hosted production has the desired canonical route:
`SharedWmScene -> DrawIrComposition -> Engine2D`. Its compositor can reject a
frame and use a fallback route, so evidence must prove the canonical route was
accepted rather than infer it from a screenshot.

The canonical x86_64 SimpleOS entry is
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`, which uses
`engine2d_wm_frame_executor.spl`. The older `wm_entry.spl` is a legacy raw path
and cannot establish completion for this feature.

## Existing Evidence and Gaps

The current QEMU fullscreen evidence demonstrates a nonblank 3840x2160
`pmemsave` framebuffer and input-driven pixel change. It does not record the
resolved theme identity, theme revision, structured glass properties, or the
first unavailable GPU/readback proof rung. Existing focused contracts also
contain stale clock-region expectations and intentional failure placeholders.

## Root-Cause Direction

Resolve one theme package once, project typed semantic tokens into both WM
chrome and Web CSS, preserve glass properties through computed style and Draw
IR, and make host/QEMU evidence report the same theme fingerprint. Do not add a
private renderer or claim legacy `wm_entry.spl` evidence as canonical.
