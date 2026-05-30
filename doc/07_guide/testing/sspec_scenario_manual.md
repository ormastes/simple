# SSpec Scenario Manual Guide

Use this guide when writing SPipe/SSpec tests whose generated `doc/06_spec/...`
output should read like a scenario-based manual.

## Principle

Executable tests are the source of truth, but the generated document is a
manual. A reader should see scenario intent, ordered user/system steps, and
evidence under the relevant step before they see test mechanics.

## Scenario Shape

Prefer small helper/checker methods with human step text:

```simple
@step "User opens the app"
fn open_app():
    ...

@step "User enters login {name}"
fn enter_login(name: text, password: text):
    ...

@step "Then login succeeds"
fn Then_login_succeeds():
    expect(session.status).to_equal("signed-in")
```

Use scenarios as manual flows:

```simple
@capture
it "user logs in":
    user.open_app()
    user.enter_login("demo", "pass")
    Then_login_succeeds()
```

Generated docs should render the step prose and captures first. Runnable code
belongs in a folded `Executable SPipe` block.

Current docgen derives starter manual steps from call-like scenario lines and
keeps assertion mechanics in the folded executable block. For example,
`user.open_app()` renders as a visible `User open app` step, while
`expect(...)` and control-flow lines such as `if user.needs_login():` remain
executable detail. Nested call-like actions inside control flow can still render
as visible manual steps. Checker-style calls such as `Then_login_succeeds()`
render as `Then login succeeds`. Prefer helper names that read cleanly when
dots and underscores become words.

Use comment-form `# @step: Text` or `# @step("Text")` before a call when the
derived label is not good enough:

```simple
it "user logs in":
    user.open_app()
    # @step: Submit login form
    user.submit_login()
    # @step("Open the dashboard")
    user.open_dashboard()
```

Generated docs render `Submit login form` as the visible step and omit the
`# @step` metadata from the folded executable source.
Step-local capture metadata may sit between a step label and the action:

```simple
# @step: Submit login form
# @capture(api)
user.submit_login()
```

Empty `# @step` metadata renders a manual warning and falls back to the derived
call-like step label.
If a labeled `# @step` is not followed by a call-like manual step, generated
docs render a manual warning and omit the unused metadata from executable
source.

## Inline and Previous Scenarios

Current docgen supports comment metadata for manual visibility and previous
scenario expansion. Use `# @inline` for reusable setup flows that should not
appear as standalone manual sections:

```simple
# @inline
it "app opens":
    user.open_app()
```

Scenario expansion uses `# @inline` plus `# @prev`:

```simple
# @inline
it "app opens":
    user.open_app()

# @prev("app opens")
it "user logs in":
    user.enter_login("demo", "pass")
```

Bare `# @prev` expands the nearest previous scenario. When `# @prev` expands
successfully, generated docs do not print `Previous:`.
They show the expanded setup steps as part of the scenario.

Use `# @include("scenario title")` only when an inline scenario must appear in
the middle of another scenario:

```simple
# @inline
it "user confirms dialog":
    user.confirm_dialog()

it "user completes checkout":
    user.add_item()
    # @include("user confirms dialog")
    user.finish_checkout()
```

Do not use `it "title"` without `:` as a call; that makes the grammar and docs
ambiguous.

If `# @prev` or `# @include` references a scenario that cannot be found,
generated docs render a `Manual warnings` block and omit the metadata line from
the rendered source block.

If `# @prev` or `# @include` would create a direct scenario expansion cycle,
generated docs render a `Manual warnings` block and keep the current scenario
body usable instead of recursively expanding setup. Break the cycle by moving
shared setup into one `# @inline` scenario and including it from the visible
flows.

## Capture

Capture is off by default. A bare `@capture` enables `after_step` capture with
default kind `tui`.

Shared capture/evidence helpers live in
`src/lib/common/spec/scenario_evidence.spl`. New providers and checker helpers
should use `ScenarioCaptureMode`, `ScenarioCaptureKind`,
`ScenarioCapturePolicy`, `ScenarioEvidenceArtifact`, and
`ScenarioCheckerEvidence` instead of inventing local string constants. The
module includes pure constructors for API, execution, binary, redacted, and
checker-linked evidence.

Examples:

```simple
# @capture
it "user logs in":
    user.open_app()

    # @capture(api)
    user.submit_login()
```

Implemented docgen behavior supports comment metadata today:

- `# @capture` renders `tui after_step`.
- `# @capture(api)` renders `api after_step` for the next step.
- `# @capture(after_scenario, gui)` renders `gui after_scenario`.
- `# @capture(off)` before a step suppresses inherited scenario capture for
  that step.
- Scenario and step-local capture policies appear under derived manual steps
  when the next source line can be rendered as a manual step.
- Scenario-level `after_scenario` capture attaches to the final derived manual
  step instead of every step.
- If no manual step can be derived, capture metadata falls back to a compact
  scenario/step capture summary.
- `# @capture(off)` is silent in fallback summaries.
- Capture metadata comments are omitted from the rendered source block.

Supported capture modes:

- `off`
- `after_step`
- `after_scenario`
- `on_failure`

Supported capture kinds:

- `tui`
- `gui`
- `text`
- `api`
- `protocol`
- `exec`
- `binary`
- `log`
- `artifact`

Capture can be configured at root, folder, file, scenario, function/checker, or
single-step scope. Closest scope wins.

Invalid capture metadata such as `# @capture(video)` renders a manual warning
instead of silently falling back to a misleading default capture. Use only the
supported modes and kinds above.

## Environmental Tests

System and environmental tests use the same manual form. Their evidence may be:

- `exec`: command, args, stdin/input triggers, stdout/stderr, exit code.
- `protocol`: MCP, DAP, QMP, serial, HTTP, or other request/response frames.
- `api`: request parameters, response fields, status, headers.
- `binary`: raw bytes plus decoded fields and comments.
- `log`: relevant runtime or hardware logs.

Do not force environmental tests to fake screenshots. Capture the evidence a
human manual would need to reproduce and understand the scenario.

## MCP Manual Pattern

MCP specs are the first exemplar for non-UI scenario manuals. A good generated
MCP manual should show:

1. Operator starts or connects to the MCP server.
2. Operator sends `initialize`.
3. Operator sends `initialized` and requests `tools/list`.
4. Operator calls one representative tool.
5. Operator verifies tool-level error behavior.
6. Protocol/API/exec/log evidence appears under each step.

Fold schema inventories, gap matrices, stress loops, and large JSON payloads by
default. Use `doc/03_plan/sys_test/mcp_scenario_manual_quality.md` as the target
review plan.

## Manual Visibility

Very detailed test scenarios should not clutter the main manual. Use visibility
policy by folder/file/scenario/step:

- `manual(show)` — normal manual content.
- `manual(folded)` — advanced or edge content shown collapsed.
- `manual(skip)` — executable test is omitted from manual generation.
- `manual(detail)` — folded implementation/test details.

Use folded mode for edge cases, stress cases, protocol matrix rows, and internal
helper checks unless they are part of the primary user/admin/operator flow.

Implemented file-level comment metadata:

```simple
# @manual-file: folded
describe "Protocol matrix":
    it "covers a detailed row":
        ...

# @manual-file: skip
describe "Generated helper checks":
    it "checks helper plumbing":
        ...
```

Scenario-level metadata overrides the file default:

```simple
# @manual: folded
it "covers an advanced edge case":
    ...

# @manual: skip
it "checks helper plumbing":
    ...

# @manual: detail
it "documents implementation detail":
    ...

# @manual: show
slow_it "important slow operator flow":
    ...
```

`slow_it` scenarios fold by default in generated docs. Use `# @manual: show`
only when the slow scenario is part of the primary manual.

Folder and root defaults use the nearest config file named `.sspec-manual` or
`sspec-manual.sdn`:

```text
manual: folded
```

Valid values are `show`, `folded`, `detail`, and `skip`. Precedence is:
scenario comment, file comment, nearest folder/root config, built-in default.
Invalid manual visibility metadata renders a manual warning and leaves the
scenario visible by default so the generated doc is still reviewable.

## Quality Loop

After writing or changing a scenario:

1. Generate the doc with `bin/simple spipe-docgen <spec> --output doc/06_spec`.
2. Read the generated doc as if it were a hand-written manual.
3. If it reads like code or test plumbing, improve `@step`, helper names,
   visibility, capture kind, or checker/capture output.
4. Repeat until the manual is useful without opening the source test.
