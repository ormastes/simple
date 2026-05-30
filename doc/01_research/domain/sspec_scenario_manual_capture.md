<!-- codex-research -->
# Domain Research: Scenario Manuals and Typed Test Evidence

**Date:** 2026-05-30
**Scope:** Prior art for generated scenario manuals, BDD reports, and capture
evidence used by UI, API, execution, and environmental tests.

## Findings

### BDD scenarios should read as behavior, not test mechanics

Cucumber-style BDD documentation treats a scenario as the unit a reader follows:
a title, ordered steps, and attachments/evidence associated with those steps.
That maps well to SPipe `it` blocks when helper calls can render human prose.

Useful source:
- Cucumber documentation: https://cucumber.io/docs/gherkin/

### Step-local attachments are the right evidence model

Allure reports organize results around test steps and attachments. Attachments
can be screenshots, text, logs, request/response data, or arbitrary files. This
supports one shared `EvidenceArtifact` model instead of separate screenshot,
TUI, log, and artifact paths.

Useful sources:
- Allure attachments: https://allurereport.org/docs/attachments/
- Allure steps: https://allurereport.org/docs/steps/

### UI capture should preserve action context

Playwright traces combine actions, screenshots, DOM snapshots, console output,
and network activity so the reader can inspect what happened at each action.
SPipe does not need the whole trace viewer first, but the manual should render
captures under the step that caused them.

Useful source:
- Playwright trace viewer: https://playwright.dev/docs/trace-viewer

### Test reports support mixed media

pytest-html style reports support "extras" such as text, images, URLs, and
HTML. This confirms that generated SPipe docs should support multiple evidence
kinds rather than treating capture as only GUI/TUI.

Useful source:
- pytest-html user guide: https://pytest-html.readthedocs.io/en/latest/user_guide.html

## Implications For SPipe

- Use one scenario-step model that can attach typed evidence.
- Keep source code available in a folded "Executable SPipe" section.
- Render the manual view first:
  scenario title -> expanded previous/inline setup -> numbered step prose ->
  captures/evidence -> optional folded details.
- Use configuration policy by root/folder/file/scenario/step so teams can
  choose when detailed scenarios are visible, folded, or omitted.
- Environmental tests should use the same manual style. Their captures are often
  `exec`, `protocol`, `api`, `log`, or `binary`, not screenshots.
