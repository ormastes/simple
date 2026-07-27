# Web CSS Package-Authority Adapter

**Status:** fail-closed / review-cycle cap reached
**Affected lane:** canonical `generate_css("aetheric_dark")`

The uncommitted package-authority candidate correctly separates canonical
package output from the literal legacy stylesheet, but final review found two
rendering defects:

1. `generate_package_authoritative_css` appends `\\n` text rather than `\n`
   newlines between rules and before the package marker. Literal backslashes can
   corrupt CSS rule boundaries.
2. Canonical traffic-light `::before` rules set package colors but never create
   the pseudo-elements with `content`, position, and geometry. Those structural
   declarations exist only in the unreachable legacy sheet.

The package/compatibility branch and Aetheric token coverage passed inspection.
The candidate must not be committed or claimed as Web rendering evidence.

## Required repair

- Emit actual CSS newlines throughout the canonical adapter.
- Restore variable-neutral traffic-light pseudo-element structure in the
  canonical adapter; keep its colors and other visual values package-owned.
- Extend
  `test/01_unit/app/ui_web/html_css_theme_authority_spec.spl` to reject literal
  `\\n` in generated CSS and require `content`, positioning, and geometry for
  the traffic pseudo-elements.
- With an admitted self-hosted runtime, run:

  ```sh
  bin/simple test test/01_unit/app/ui_web/html_css_theme_authority_spec.spl --mode=interpreter
  bin/simple test test/01_unit/os/compositor/simple_web_window_renderer_spec.spl --mode=interpreter
  ```

- Request a fresh highest-capability source review before live Web capture.
  Do not bootstrap or substitute the Rust seed.
