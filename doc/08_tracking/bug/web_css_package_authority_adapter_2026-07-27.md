# Web CSS Package-Authority Adapter

**Status:** source fixed and independently accepted / runtime unverified
**Affected lane:** canonical `generate_css("aetheric_dark")`

The rejected package-authority candidate separated canonical package output
from the literal legacy stylesheet, but review found two rendering defects:

1. `generate_package_authoritative_css` appends `\\n` text rather than `\n`
   newlines between rules and before the package marker. Literal backslashes can
   corrupt CSS rule boundaries.
2. Canonical traffic-light `::before` rules set package colors but never create
   the pseudo-elements with `content`, position, and geometry. Those structural
   declarations exist only in the unreachable legacy sheet.

The repaired source now emits real newlines, restores traffic pseudo-element
structure, and retains the production structural/event contract for widgets,
windows, taskbar previews, dialogs, trees, resize zones, hot corners, and
responsive breakpoints. Aetheric package CSS owns every visual/material token.
Independent highest-capability review found no remaining P0/P1 source issue.

This closes the source blocker only. Live Web parser/rendering, pixels, and
events remain **RUNTIME UNVERIFIED** until an admitted self-hosted runtime can
run the focused specs and capture wrapper below.

## Remaining runtime verification

- With an admitted self-hosted runtime, run:

  ```sh
  bin/simple test test/01_unit/app/ui_web/html_css_theme_authority_spec.spl --mode=interpreter
  bin/simple test test/01_unit/os/compositor/simple_web_window_renderer_spec.spl --mode=interpreter
  ```

- Produce and verify the exact package-authority live path with the same
  admitted runtime:

  ```sh
  ADMITTED_SIMPLE=/absolute/path/to/admitted/simple
  SIMPLE_BIN="$ADMITTED_SIMPLE" sh scripts/check/produce-aetheric-host-web-gui-evidence.shs
  SIMPLE_BIN="$ADMITTED_SIMPLE" sh scripts/check/check-aetheric-host-web-gui-evidence.shs
  ```

  These wrappers exercise `simple_web_content_full_html_with_theme` using
  `aetheric_dark` and retain computed-style, HTML/WebIR-to-DrawIR, framebuffer,
  UI-access event, timing, revision, and hash evidence. The macOS Vulkan Web
  wrapper is optional backend evidence only; it is not package-authority proof.
  Do not bootstrap or substitute the Rust seed.
