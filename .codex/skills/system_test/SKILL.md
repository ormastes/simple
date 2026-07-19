---
name: system_test
description: "Codex system test design skill (Codex-specific strength). Step-based SSpec `.spl` scenario generation through the SPipe runner/docgen process. Built-in matchers only. REQ-NNN to test traceability. Test plan creation."
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

## Phase 2: Step-Based SSpec Test Generation

Generate executable SSpec `.spl` scenarios using the canonical matcher set.
SPipe runs those scenarios and generates mirrored manual docs.
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
- `to_be_true()` / `to_be_false()` — compatibility helpers; assert concrete
  values, or use `to_be(true/false)` only when the boolean itself is the behavior
- `to_raise()` — not available; test error returns via `Result<T, E>`
- Feature-specific matcher replacements — use helper functions inside SSpec
  scenarios instead

### SSpec Template

```simple
use std.spec.*

describe "<Feature Name>":
    describe "REQ-001: <requirement title>":
        it "should <expected behavior in present tense>":
            step("Open the feature surface")
            val result = <invoke feature code>
            expect(result).to_equal(<expected value>)

        it "should handle empty input":
            step("Submit empty input")
            val result = <invoke with empty>
            expect(result).to_be_nil()

        it "should reject invalid input":
            step("Submit invalid input")
            val result = <invoke with invalid>
            expect(result.error_code).to_equal("invalid-input")

    describe "REQ-002: <next requirement>":
        it "should <behavior>":
            step("Run the requested behavior")
            val result = <invoke>
            expect(result).to_contain(<expected item>)
```

### Test Quality Criteria (A-Grade)

- Every `it` block has **real assertions** (not `pass_todo`, not `expect(true).to_equal(true)`)
- Each REQ-NNN has **at least 3 tests**: happy path, edge case, error path
- Test descriptions start with "should" and describe behavior, not implementation
- No test depends on external state or other tests
- Error paths use `Result<T, E>` pattern, not exceptions
- After writing or changing an SSpec file, run
  `bin/simple spipe-docgen <spec> --output doc/06_spec --no-index`. The generator
  must report the affected spec as complete with `0 stubs`; if it reports an
  auto/manual spec as a stub, fix the spec or docgen validation before handoff.
  Use only the pure-Simple `simple-core` or `core-c-bootstrap` runtime lanes.
  An unresolved runtime symbol, nonzero exit, signal exit, or missing output is
  a FAIL; do not substitute a hand-edited manual or the Rust seed.
- Scenario-oriented specs must produce manual-quality generated docs:
  primary scenarios visible, reusable setup hidden with `@inline` and expanded
  by `@prev`/`@include`, advanced/edge/matrix/stress details folded or skipped
  by policy, and executable SSpec folded below the manual flow.
  Generated manuals must retain module-level triple-quoted scope and claim-
  boundary prose; a structurally complete manual that drops those limits is a
  documentation failure.
  Every named setup/checker helper used by a displayed scenario must appear as
  a visible manual step or in complete folded executable source.
- If a scenario claims formal verification coverage, include the formal
  evidence path and exact proof command in the test plan or generated/manual
  doc. Lean evidence must point at a checked proof lane with no `sorry` or
  `admit`; RVFI/SymbiYosys evidence must distinguish readiness from an actual
  `sby` proof pass. For Lean or BYL lanes, cite generated artifacts separately
  from durable theorem files so regeneration cannot replace manual proof
  obligations. For RISC-V lanes spanning generated RTL sidecars and Lean/BYL,
  cite `sh scripts/check/check-riscv-formal-dual-track.shs` as the aggregate
  gate so the sidecar contract self-test and manual proof layer are checked
  together. Do not let regenerated SPipe docs replace the manual Lean/BYL proof
  layer. If a generated evidence matrix reports readiness rows as `pass`, keep
  mission-critical release wording separate and cite the stricter release gate
  explicitly with `sh scripts/check/check-riscv-rtl-sby-proof.shs` and
  `sh scripts/check/check-simpleos-mission-critical-release.shs`; a readiness
  matrix pass or missing-tool blocker is not a substitute for `release_blockers=none`
  and a strict SBY proof pass.
- For broad lanes with shared interfaces, the primary/best model must define
  shared interface names, manual `step("...")` flow helper names, and
  setup/checker helper names before lower-model sidecars such as Codex Spark,
  Claude Haiku, or Claude Sonnet draft checks. The best available
  normal/highest-capability model must review and accept sidecar output before
  handoff. Placeholder helpers must fail explicitly with
  `assert(false)` or `fail(...)` until implemented; silent no-op helpers are not
  valid SSpec coverage.
- Use `step("...")` as the current manual-step helper. `Given_*`, `When_*`, and
  `Then_*` helpers are legacy and should not be introduced in new specs.
- Use `@step` metadata only when labeling an existing helper/checker call that
  cannot be replaced cleanly with `step("...")`.
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
  functions inside normal SSpec `it` blocks. These helpers must assert rendered
  state, not merely call the renderer: check Draw IR/object state, scene nodes,
  layout boxes, visible text, readback pixels, hashes, or diffs that prove the
  expected surface exists.
- GUI/web font specs assert semantic `DrawIrComposition` text/style before
  backend/readback evidence. When vector text is enabled, `FontRenderBatch`
  remains transient material inside the Engine2D executor; an app-private font
  draw path or Engine3D HUD/world shortcut is not valid GUI/web/2D evidence.
  WM route evidence must distinguish the canonical `SharedWmScene ->
  DrawIrComposition -> Engine2D` executor from compatibility direct
  backend/pixel-buffer renderers. A builder-only fixture is supporting evidence:
  production acceptance must exercise the real hosted frame owner, canonical
  SimpleOS entry wiring, and independent QEMU framebuffer pixels. Platform
  backends present final pixels; they do not own a second font path.
- Shared multilingual font specs use the frozen steps, setup helpers, and
  checkers in `doc/03_plan/sys_test/shared_multilingual_gpu_fonts.md`; do not
  rename them or introduce parallel vocabulary. Exact-face acceptance is
  limited to the witnesses the shaping gate proves: the pinned Hindi `हिन्दी`
  `dev2` case and the exact pinned Arabic `العربية` / Urdu `اردو` lookup-vector
  cases are accepted. The Arabic/Urdu acceptance is witness-specific after
  Script/LangSys validation; it is not general GSUB/GPOS, mark, BiDi, or
  positioning support. A single pinned monochrome `U+1F600` emoji candidate
  may promote only after its exact-face shape-to-`FontRenderBatch` gate passes;
  parser/cmap/raster evidence alone is insufficient. Variation-selector,
  modifier, ZWJ, color, and multi-codepoint emoji remain fail-closed.
  The final irreversible registered-only SimpleOS scenario must register the
  exact Arabic and Devanagari bytes, shape the accepted Arabic/Urdu and Hindi
  witnesses without host font ABI or filesystem access, keep Draw IR
  handle-free, and prepare nonempty material through the existing selected-byte
  `FontRenderer`. This source/spec result is not QEMU framebuffer evidence.
  Vulkan font promotion requires `artifact_mode=precompiled-spirv` and the exact
  pinned artifact hash; runtime GLSL may be diagnostic execution but cannot
  satisfy native promotion. The checker requires extracted optimization/font
  source bytes to match their emitter-declared hashes and rejects malformed hashes
  before compilation. A well-formed stale Vulkan source may compile and retain
  its `.comp`/`.spv` candidate for review, but its evidence remains invalid;
  admission requires both source and artifact pins to match.
  The portable checker aggregates only targets named by
  `PORTABLE_COMPUTE_TARGETS` and rejects a source whose emitted semantics does
  not equal `PORTABLE_COMPUTE_EXPECTED_SEMANTICS`. Phase one requires
  `candidate_compiled=true` and `artifact_validated=true`, with compiler and
  validator path/version/SHA-256 provenance and a passing `spirv-val` row for
  Vulkan. Stale pins must report `pinned_verified=false`. After independent
  review updates tracked source/artifact pins, a reproducing phase-two run must
  report `pinned_verified=true`; never update pins merely to green phase one.
  Compiled native evidence must name the Simple-emitted font companion, prove
  its versioned exported symbol, and prove the promoted runtime loaded that same
  artifact; a handwritten PTX or independently generated SPIR-V blob is not
  emitter provenance. CUDA font execution must use the separately
  source-tracked Simple-generated companion after runtime PTX hash, entry, and
  program-version checks pass; checker/SPipe exact equality must bind its pinned
  source and emitter-version hashes to the current Simple emission. The default
  CUDA 2D module must not provide the font entry.
  Production CUDA loading additionally requires packaged or tracked generated
  PTX bound to an immutable trusted hash and program version; ignored `build/`
  output and caller-provided adjacent hashes cannot satisfy that trust gate.
  When a producer emits selected shaping, assert that the handle-free
  `DrawIrGlyphRunPayload` survives SDN round-trip with identical glyph IDs,
  positions, and logical clusters. The Engine2D executor must reject a missing
  or malformed shaped payload and must consume serialized advances through the
  canonical `FontRenderer`; do not serialize face handles, atlases, caches, or
  backend resources into Draw IR.
  Runtime configuration evidence must use the single text-layout-owned config
  and prove each identity dimension reaches bitmap, selected-vector, shaped,
  Engine2D, and Engine3D material. Assert `Suggested` named-target/remaining-
  canonical-GPUs/CPU, `Preferred` named-target/CPU, and `Required` named-target-
  only behavior. Assert `Suggested(auto)` uses the engine's executable adapter
  order. Spell the canonical target `rocm` and separately prove the `hip` alias
  selects identical HIP emission; Preferred/Required with `auto` and unknown targets reject before any
  cache, counter, upload, framebuffer, or backend mutation.
  Unsupported rendering modes or CTM must fail before cache generation,
  telemetry, upload, or backend state changes.
  Before accepting deployed font execution, prove the candidate uses the
  four-argument `rt_env_set(key_ptr, key_len, value_ptr, value_len)` ABI and
  passes one tiny `check` fixture. A bootstrap-only stage compiler, a Rust
  seed, or a candidate whose full-CLI closure has unresolved runtime
  symbols is blocker evidence, not an executable font PASS.
  The canonical runner and the pure test runner must reuse
  `build_interpreter_result_wrapper`; it appends `print_summary`,
  `get_executed_test_count`, and `get_exit_code` checks inside the interpreted source.
  `CompileResult.Success` alone is false green because matcher failures update
  spec state without raising. Before trusting the runner, require exit 1 plus
  `test-runner: spec failed` from
  `scripts/check/fixtures/font_evidence_runner_fail_spec.spl`, and exit 1 plus
  `test-runner: no examples executed` from
  `scripts/check/fixtures/font_evidence_runner_empty_spec.spl`. Reject usage
  exit 2, timeout 124, signal exit 139, and missing markers. Retain the exact
  commands, runner binary SHA-256, and both logs under
  `build/test-artifacts/shared_multilingual_gpu_fonts/runner-calibration/`.
  Shaped pixel evidence must include a nonzero bearing or GPOS offset and check
  the full CPU/device pixels. Pen positions are +Y-down baseline offsets;
  OpenType y offsets are negated, and quad top-left is
  `(pen_x + bearing_x, ascent + pen_y - bearing_y - height)`.
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
  - CLI/TUI scenario manuals should show the capture path and a compact embedded
    sample when the output is small enough to review inline; use
    `test/02_integration/app/ide/ide_feature_check_integration_spec.spl` as the
    current step-based SSpec model.
  - HTML-backed GUI specs capture source HTML/visible text and check user-visible text before screenshot checks.
  - GUI specs capture screenshots/goldens/diffs under `doc/06_spec/image/<spec-relative-path>/` when HTML is unavailable or insufficient.
  - Draw IR and 2D specs capture or assert object/command state where possible
    before falling back to screenshots.
  - Evidence paths appear in `**Screenshots:**` or `**TUI Captures:**` metadata so generated `doc/06_spec/...` docs can render them according to evidence display policy.
  - Raster evidence (`.png`, `.jpg`, `.jpeg`, `.webp`, `.gif`, `.ppm`) is tracked by Git LFS.
- After adding or moving UI-facing app feature specs, run
  `test/03_system/app/testing/feature/ui_sspec_evidence_audit_spec.spl` so the
  critical UI lane keeps executable specs, mirrored `doc/06_spec/03_system/app`
  manuals, and visible evidence markers.
- SGTTI must remain zero-overhead outside explicit test/debug builds. Specs that
  add SGTTI-backed TUI/GUI evidence must also prove the normal production
  entrypoint does not import `std.ui_test.sgtti`, `SgttiTestDriver`, or the
  SGTTI capture/debug surface. The test/debug entrypoint may import SGTTI; the
  default product/runner path must not construct snapshots, poll UI state, or
  allocate capture nodes when SGTTI is compile-time disabled or absent.
- Draw IR layout/style parity specs should capture structured Protocol-v2
  evidence when available: use `draw-ir/diff?baseline=...&capability=draw_ir`
  or `common.ui.draw_ir_diff` for stable-id geometry, border, color, style, and
  text-bound deltas; screenshots are supporting evidence, not the only oracle.
- GUI render-location specs should prove "what rendered where" through
  `draw-ir/layout?id=...&capability=draw_ir` or `expect_draw` before relying on
  screenshot pixels: assert stable id, kind/role, geometry, hit rect, parent,
  and computed style.
- Environmental tests should capture command/API/protocol/binary/log evidence
  when that is more meaningful than a screenshot.
- MCP command-line server specs should use a reusable helper that launches the
  actual wrapper command, sends `initialize`, `notifications/initialized`, and
  `tools/list`, and asserts readiness JSON, exit code, elapsed time, JSON-RPC
  response, tools array, and an expected tool marker. Keep the helper pure
  Simple/stdlib: do not add direct `rt_*` externs, Node.js wrappers, or hosted
  fallback requirements. Prefer JSON Lines input when validating wrappers that
  advertise JSONL auto-detect; use framed `Content-Length` only for servers
  whose shared transport is known to support multi-message framed stdin.
  Include all local Simple-created MCP wrappers in one system spec when the
  contract is "launch by command line and handshake within a time limit".
  Bootstrap acceptance parameterizes that same checker with the exact fresh
  Stage 5 MCP/LSP paths, requires successful `simple_status` and `lsp_symbols`
  calls, and fails on missing/stale artifacts, runtime stubs, source or Rust-seed
  fallback, nonzero exit, timeout, malformed frames, or error responses. Run it
  for every bootstrap route that produces a full MCP/LSP output pair. The
  separate Stage 2 MCP spec covers only its single cached MCP artifact; earlier
  stages and `--no-mcp` supply no full-pair MCP/LSP acceptance evidence.
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

- Executable SSpec tests live under `test/`; generated/manual SPipe docs live under
  `doc/06_spec/`.
- `doc/06_spec` must not contain executable `.spl` specs. Run
  `find doc/06_spec -name '*_spec.spl' | wc -l` before completion and require
  `0`.
- Generated manuals must be current for every changed SSpec and must not be
  reported by `spipe-docgen` as stubs. Review the mirrored `.md` to confirm it
  contains visible scenario steps plus folded executable SSpec blocks.
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

Interpreter `it` bodies may execute, but the outer summary, exit status, and
`CompileResult.Success` are not trustworthy assertion results without the
counter guards above. Native acceptance uses:

```bash
SIMPLE_NO_STUB_FALLBACK=1 bin/simple test path/to/spec.spl --mode=native
```

## Multi-LLM Collaboration

- If other LLMs wrote test specs, review quality and extend — never overwrite
- Codex is the preferred test designer in cooperative mode
- Tag Codex-produced tests with `# codex-system-test` comment

## Rules

- Canonical matchers only in new specs; add helper functions inside scenarios
  instead of custom matcher replacements
- Every REQ-NNN must have test coverage — zero is a FAIL
- Do not use `to_be_true()` / `to_be_false()`; assert concrete values, or use
  `to_be(true/false)` only when the boolean itself is the behavior.
- All test code in `.spl` — no Python, no Bash
- Generics use `<>` not `[]`
- NO inheritance in test helpers — use composition
- NEVER skip or ignore failing tests without user approval
- Do not write short-grammar tests that only prove a longer equivalent form; the compact token/form itself must appear in executable coverage.
