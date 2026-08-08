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

## 2026-05-31 Addendum: HTML Capture and Checking

User request: extend SSpec capture/check support so GUI captures from
Simple/Web-backed surfaces prefer HTML capture when possible, expose visible
HTML text for checks, and research HTML checking tools.

Findings:

- Nu Html Checker / Validator.nu is the standards-oriented HTML5 validation
  path and exposes a service/API model for validating submitted HTML. It is
  best suited for conformance checks on full HTML documents.
  Source: https://about.validator.nu/
- `html-validate` is an offline HTML5 validator with CLI and API support,
  including inline string validation. It is a good fit for local/CI checks and
  eventually for a first native integration behind an SSpec HTML checker.
  Sources:
  - https://html-validate.org/usage/
  - https://html-validate.org/usage/cli.html
  - https://html-validate.org/guide/api/getting-started.html
- Playwright documents accessibility testing through `@axe-core/playwright`.
  This is a good fit when the HTML state only exists after a user interaction
  or when the check must run against a browser DOM rather than a static string.
  Source: https://playwright.dev/docs/next/accessibility-testing

Implications for SPipe:

- `gui` capture should stay available for screenshot/image evidence, but when a
  GUI surface is backed by Simple Web/HTML, the provider should emit `html`
  evidence first because it is inspectable, diffable, and checkable.
- HTML checks should distinguish raw markup containment from visible text
  checks. Visible text checks are the safer default for manuals because they
  verify what a user can read instead of matching hidden attributes or scripts.
- SSpec should model checker tool output separately from the initial heuristic
  helpers so later providers can attach `nu_html_checker`, `html_validate`,
  `axe_core`, or `playwright_locator` results without changing manual output.
- Evidence display needs a user-selected policy. The practical default is to
  embed TUI captures because they are compact text/image state and link other
  artifacts because screenshots, logs, protocol dumps, and binary artifacts can
  dominate generated manuals. Users still need explicit `links` and `embed_all`
  modes for review workflows that prefer compact docs or fully visual docs.
