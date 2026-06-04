---
name: system_test
description: "Codex system test design skill (Codex-specific strength). SPipe BDD test generation with built-in matchers only. REQ-NNN to test traceability. Test plan creation."
---

# System Test Design — Codex (Codex-Specific Strength)

**Cooperative Phase:** Design support (Step 4) and standalone test design
**Self-sufficient.** Can generate system tests independently given requirements.

Codex excels at systematic test generation with full requirement traceability. Use this skill for test-focused tasks.

## Tools

- **Simple MCP** — query codebase structure, existing tests
- **Simple LSP MCP** — symbol lookup, type signatures for test targets

## Prerequisites

| Artifact | Path | If missing |
|----------|------|-----------|
| Requirements | `doc/02_requirements/feature/<feature>.md` | Need requirements first — run research |
| NFR | `doc/02_requirements/nfr/<feature>.md` | Need NFR first — run research |

## Phase 1: Requirement Extraction

- Parse all REQ-NNN from requirements document
- Identify testable behaviors per requirement
- Map edge cases and error paths

## Phase 2: SPipe BDD Test Generation

Generate test specs using **built-in matchers only**.
Executable specs belong under `test/...`; `doc/06_spec/...` is reserved for
generated/manual scenario documentation derived from those specs.

### Built-in Matchers (ONLY these are allowed)

| Matcher | Usage |
|---------|-------|
| `to_equal(expected)` | Exact equality |
| `to_be(expected)` | Identity/reference equality |
| `to_be_nil()` | Nil check |
| `to_contain(item)` | Collection/string contains |
| `to_start_with(prefix)` | String starts with |
| `to_end_with(suffix)` | String ends with |
| `to_be_greater_than(val)` | Numeric greater than |
| `to_be_less_than(val)` | Numeric less than |

**Forbidden patterns:**
- `to_be_true()` — use `to_equal(true)` instead
- `to_be_false()` — use `to_equal(false)` instead
- `to_raise()` — not available; test error returns via `Result<T, E>`
- Custom matchers — not supported

### SPipe Template

```simple
use std.spec.SPipe

describe "<Feature Name>":
    describe "REQ-001: <requirement title>":
        it "should <expected behavior in present tense>":
            val result = <invoke feature code>
            expect(result).to_equal(<expected value>)

        it "should handle empty input":
            val result = <invoke with empty>
            expect(result).to_be_nil()

        it "should reject invalid input":
            val result = <invoke with invalid>
            expect(result.error?).to_equal(true)

    describe "REQ-002: <next requirement>":
        it "should <behavior>":
            val result = <invoke>
            expect(result).to_contain(<expected item>)
```

### Test Quality Criteria (A-Grade)

- Every `it` block has **real assertions** (not `pass_todo`, not `expect(true).to_equal(true)`)
- Each REQ-NNN has **at least 3 tests**: happy path, edge case, error path
- Test descriptions start with "should" and describe behavior, not implementation
- No test depends on external state or other tests
- Error paths use `Result<T, E>` pattern, not exceptions
- Scenario-oriented specs must produce manual-quality generated docs:
  primary scenarios visible, reusable setup hidden with `@inline` and expanded
  by `@prev`/`@include`, advanced/edge/matrix/stress details folded or skipped
  by policy, and executable SPipe folded below the manual flow.
- Use `@step` helper/checker prose when function names alone would not read like
  manual steps.
- Capture is off by default. Bare `@capture` enables after-step `tui` capture.
  Use typed capture kinds for the evidence the reader needs: `tui`, `gui`,
  `html`, `text`, `api`, `protocol`, `exec`, `binary`, `log`, or `artifact`.
- For Simple Web or HTML-backed GUI surfaces, prefer `html` capture and
  visible-text HTML checks; use `gui` screenshot capture as fallback evidence
  when HTML cannot be captured.
- GUI behavior specs must also drive or query the actual surface through the
  Simple UI access contract when the repository exposes it: `ui_access_snapshot`,
  `ui_access_surface`, `ui_access_find`, `ui_access_act`, `ui_access_history`,
  `ui_access_observe`, or `ui_access_state`. CLI/MCP wrappers such as
  `simple play wm-text-*` and `play_wm_text_*` are acceptable adapters. A
  screenshot-only pass is evidence, not interaction coverage.
- Evidence display is user-selectable with `# @evidence-display: embed_tui`,
  `links`, or `embed_all`. Default to `embed_tui`: embed TUI evidence and link
  screenshots, logs, protocol dumps, binary artifacts, and other non-TUI files.
- Capture and manual visibility policy may be set at root, folder, file,
  scenario, or step scope; the nearest explicit scope wins, and root default
  remains capture off.
- UI-facing specs include visible-state capture evidence when practical:
  - TUI specs capture text or ANSI output under `build/test-artifacts/<spec-relative-path>/`.
  - HTML-backed GUI specs capture source HTML/visible text and check user-visible text before screenshot checks.
  - GUI specs capture screenshots/goldens/diffs under `doc/06_spec/image/<spec-relative-path>/` when HTML is unavailable or insufficient.
  - Evidence paths appear in `**Screenshots:**` or `**TUI Captures:**` metadata so generated `doc/06_spec/...` docs can render them according to evidence display policy.
  - Raster evidence (`.png`, `.jpg`, `.jpeg`, `.webp`, `.gif`, `.ppm`) is tracked by Git LFS.
- Environmental tests should capture command/API/protocol/binary/log evidence
  when that is more meaningful than a screenshot.
- Short grammar features must have runtime-specific coverage:
  - Interpreter specs may cover pipe-forward, composition, placeholder lambdas, method references, optional access, and compact DSL forms.
  - Native specs must cover only compact forms intended to work in native mode.
  - Native short-grammar evidence must be run with `SIMPLE_NO_STUB_FALLBACK=1` so codegen stub fallback cannot masquerade as a pass.
  - A spec claiming walrus shorthand support must use the actual `:=` token, not `val` as a substitute.

## Phase 3: Traceability Matrix

Create a traceability matrix linking requirements to tests:

```markdown
| REQ | Description | Test File | Test Cases | Coverage |
|-----|-------------|-----------|------------|----------|
| REQ-001 | <desc> | <path>_spec.spl | 3 | Full |
| REQ-002 | <desc> | <path>_spec.spl | 4 | Full |
| REQ-003 | <desc> | — | 0 | MISSING |
```

Any REQ with 0 test cases is a **FAIL** — must be addressed.

### Layout and Traceability

- Executable tests live under `test/`; generated/manual SPipe docs live under
  `doc/06_spec/`.
- `doc/06_spec` must not contain executable `.spl` specs. Run
  `find doc/06_spec -name '*_spec.spl' | wc -l` before completion and require
  `0`.
- Mirror the executable path after stripping `test/`, for example
  `test/03_system/feature/usage/math_blocks_spec.spl` ->
  `doc/06_spec/feature/usage/math_blocks_spec.md`.
- Keep requirement, research, design, architecture, plan, generated spec,
  implementation, guide, and executable test artifacts on the same feature slug.
- Include both the generated spec/manual path and executable `test/...` path in
  the traceability matrix.
- For TUI/GUI specs, include the capture artifact path and generated embedded
  evidence path in the traceability matrix or test plan.

## Phase 4: Test Plan Document

Create test plan with:
- Scope (what is tested, what is excluded)
- Test environment requirements
- Execution order and dependencies
- Pass/fail criteria
- Risk areas needing extra coverage
- Manual rendering policy: which scenarios are visible, folded, skipped, or
  detail-only in generated `doc/06_spec/...`
- Capture plan by evidence kind and scope

Output: `doc/03_plan/sys_test/<feature>.md`

## Artifacts Produced

| Artifact | Path |
|----------|------|
| System test specs | `test/<mirrored-test-path>/<feature>_spec.spl` |
| Generated spec docs | `doc/06_spec/<mirrored-test-path>/<feature>_spec.md` |
| Test plan | `doc/03_plan/sys_test/<feature>.md` |
| Traceability matrix | Included in test plan |

## Interpreter Mode Limitation

**Important:** The test runner in interpreter mode only verifies file loading, NOT `it` block execution. The `it` block bodies do not execute in interpreter mode. Use compiled mode for actual test execution:

```bash
bin/simple test path/to/spec.spl          # Interpreter mode (loading only)
bin/simple test path/to/spec.spl --native  # Compiled mode (full execution)
```

## Multi-LLM Collaboration

- If other LLMs wrote test specs, review quality and extend — never overwrite
- Codex is the preferred test designer in cooperative mode
- Tag Codex-produced tests with `# codex-system-test` comment

## Rules

- Built-in matchers ONLY — no custom matchers
- Every REQ-NNN must have test coverage — zero is a FAIL
- Use `to_equal(true)` not `to_be_true()`
- All test code in `.spl` — no Python, no Bash
- Generics use `<>` not `[]`
- NO inheritance in test helpers — use composition
- NEVER skip or ignore failing tests without user approval
- Do not write short-grammar tests that only prove a longer equivalent form; the compact token/form itself must appear in executable coverage.
