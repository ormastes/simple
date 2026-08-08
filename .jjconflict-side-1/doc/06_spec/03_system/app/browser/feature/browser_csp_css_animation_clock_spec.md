# CSP-denied script CSS animation clock

Executable scenario:
`test/03_system/app/browser/feature/browser_csp_css_animation_clock_spec.spl`

**Docgen:** pending; this lane intentionally does not run bootstrap, seed, or
runtime tooling.

| Requirement | Evidence |
| --- | --- |
| REQ-WEB-BROWSER-003 | A CSS keyframe advances from exact red to exact midpoint color under CSP sandbox. |
| REQ-WEB-BROWSER-004 | Both frames lower from web layout to `DrawIrComposition` and Engine2D pixels. |
| REQ-WEB-BROWSER-005 | The response-header sandbox rejects direct JavaScript evaluation. |
| REQ-WEB-BROWSER-006 | Timer and rAF source stays inert while the shared monotonic clock reaches 500 ms. |
| REQ-WEB-BROWSER-012 | CSP is committed before document script admission and remains enforced after clock advancement. |
| REQ-WEB-BROWSER-021 | The executable scenario retains named setup/check helpers and exact assertions. |

1. Commit a script-denying response-header CSP with one CSS animation and
   JavaScript timer/rAF mutation traps (`setup_csp_clock_fixture`).
2. Advance the monotonic browser clock to 500 ms without running callbacks
   (`check_clock_advanced_without_callbacks`).
3. Verify the CSP sandbox, absent runtime, callback count, title, body, and
   direct evaluation rejection (`check_scripts_denied`).
4. Lower the start and midpoint frames through web layout and canonical Draw
   IR, then verify exact commands and Engine2D red/midpoint/white pixel counts
   (`check_css_frame_progressed`).

## Folded executable scenario

```simple
describe "REQ-WEB-BROWSER-003/004/005/006/012: CSP animation clock":
    # @manual: show
    # @capture(html)
    # @capture(artifact)
    it "should advance CSS animation frames while scripts stay denied":
        step("Commit a script-denying CSP")
        val session = setup_csp_clock_fixture()
        step("Advance the monotonic browser clock")
        check_clock_advanced_without_callbacks(session)
        step("Reject script callbacks")
        check_scripts_denied(session)
        step("Render the next CSS animation frame")
        check_css_frame_progressed(session)
```
