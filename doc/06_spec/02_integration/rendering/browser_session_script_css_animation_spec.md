# BrowserSession Script and CSS Animation Rendering Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 5 | 5 | 0 | 0 |

## Scenarios

- Simple Script creates the initial DOM/CSS frame, then JavaScript selects that
  same newly created element in `requestAnimationFrame`, mutates its style, and
  Engine2D renders a distinct frame.
- A runtime created after the browser clock advances keeps relative
  `setTimeout` deadlines instead of firing on the next tick.
- CSS `@keyframes` alone renders distinct start, midpoint, and forwards-filled
  end frames on the BrowserSession monotonic clock.
- Case-sensitive animation names match, and an external stylesheet establishes
  its animation epoch when it finishes loading rather than at document commit.

Requirement trace: REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-005,
REQ-WEB-BROWSER-006, REQ-WEB-BROWSER-007, REQ-WEB-BROWSER-017.

Source:
`test/02_integration/rendering/browser_session_script_css_animation_spec.spl`

Target fixture: `test/fixtures/browser_script_css_animation/main.spl`

Updated: 2026-07-27.
