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

Generate test specs using the canonical SPipe matcher set.
Executable specs belong under `test/...`; `doc/06_spec/...` is reserved for
generated/manual scenario documentation derived from those specs.

### Canonical Matchers

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

**Do not use in new specs:**
- `to_be_true()` — compatibility helper; use `to_equal(true)` instead
- `to_be_false()` — compatibility helper; use `to_equal(false)` instead
- `to_raise()` — not available; test error returns via `Result<T, E>`
- Feature-specific matcher replacements — use helper functions inside SPipe
  scenarios instead

### SPipe Template

```simple
use std.spec

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
- GUI, Web, 2D, and WASM rendering specs should use `expect_draw`-style helper
  functions inside normal SPipe `it` blocks. These helpers must assert rendered
  state, not merely call the renderer: check Draw IR/object state, scene nodes,
  layout boxes, visible text, readback pixels, hashes, or diffs that prove the
  expected surface exists.
- For HTML/CSS/WASM-backed surfaces, prefer HTML or DOM-visible-text checks
  before raster checks. Assert semantic text, attributes, layout-relevant
  objects, or canvas/wasm bridge state when available; use GUI screenshots,
  goldens, and pixel diffs as fallback or supplemental evidence.
- Rendering checks must not use placeholder assertions such as `pass_todo`,
  `expect(true).to_equal(true)`, or empty helper bodies. If the renderer cannot
  be executed on the host, skip with a concrete reason or assert an available
  non-raster oracle such as generated Draw IR, object state, or captured HTML.
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
  - Draw IR and 2D specs capture or assert object/command state where possible
    before falling back to screenshots.
  - Evidence paths appear in `**Screenshots:**` or `**TUI Captures:**` metadata so generated `doc/06_spec/...` docs can render them according to evidence display policy.
  - Raster evidence (`.png`, `.jpg`, `.jpeg`, `.webp`, `.gif`, `.ppm`) is tracked by Git LFS.
- Draw IR layout/style parity specs should capture structured Protocol-v2
  evidence when available: use `draw-ir/diff?baseline=...&capability=draw_ir`
  or `common.ui.draw_ir_diff` for stable-id geometry, border, color, style, and
  text-bound deltas; screenshots are supporting evidence, not the only oracle.
- Environmental tests should capture command/API/protocol/binary/log evidence
  when that is more meaningful than a screenshot.
- Short grammar features must have runtime-specific coverage:
  - Interpreter specs may cover pipe-forward, composition, placeholder lambdas, method references, optional access, and compact DSL forms.
  - Native specs must cover only compact forms intended to work in native mode.
  - Native short-grammar evidence must be run with `SIMPLE_NO_STUB_FALLBACK=1` so codegen stub fallback cannot masquerade as a pass.
  - A spec claiming walrus shorthand support must use the actual `:=` token, not `val` as a substitute.
- Startup-sensitive specs must preserve the app startup fast path:
  - If the change touches `simple run`, file-argument startup parsing,
    `get_cli_args`, `std.cli`, `.shs` dispatch, mmap/read-ahead startup
    loading, launch metadata, or startup dynlib policy, include
    `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` in the test
    plan and traceability.
  - Generated docs must mirror that spec at
    `doc/06_spec/02_integration/app/startup_argparse_mmap_perf_spec.md`.
  - Do not replace the compact startup path with a compile/JIT workaround just
    to make a test pass; fix the fast path or record a concrete bug.
  - If the change touches dynSMF precompiled artifacts or compiling SMF while
    interpreter startup continues, include both
    `test/01_unit/os/smf/dynsmf_session_spec.spl` and
    `test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl`. Tests
    must prove `compile_background` evidence for at least one non-GUI manifest
    entry and one GUI-related entry, and must also prove checked autoload still
    fails closed until a valid `SMF\0` artifact exists.

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
  `doc/06_spec/03_system/feature/usage/math_blocks_spec.md`.
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

- Canonical matchers only in new specs; add helper functions inside scenarios
  instead of custom matcher replacements
- Every REQ-NNN must have test coverage — zero is a FAIL
- Use `to_equal(true)` not compatibility helpers such as `to_be_true()`
- All test code in `.spl` — no Python, no Bash
- Generics use `<>` not `[]`
- NO inheritance in test helpers — use composition
- NEVER skip or ignore failing tests without user approval
- Do not write short-grammar tests that only prove a longer equivalent form; the compact token/form itself must appear in executable coverage.
