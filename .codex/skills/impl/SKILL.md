---
name: impl
description: "Codex implementation skill. 15-phase workflow from research through verification. Self-sufficient — if research, requirements, or design missing, creates them first. Code in .spl only, 80%+ branch coverage, stub prevention gate."
---

# Impl — Codex Self-Sufficient 15-Phase Workflow

**Cooperative Phase:** Implementation (any step — self-sufficient)
**Self-sufficient.** If research, requirements, or design missing, does them first (phases 1-5).

## Tools

- **Simple MCP** — query codebase structure, module graph
- **Simple LSP MCP** — symbol lookup, type checking, go-to-definition
- **Context7 MCP** — external library documentation

## Prerequisites Check

| Artifact | Path | If exists, skip to |
|----------|------|--------------------|
| Research | `doc/01_research/local/<feature>.md` | Phase 4 |
| Requirements | `doc/02_requirements/feature/<feature>.md` | Phase 4 |
| Architecture | `doc/04_architecture/<feature>.md` | Phase 6 |
| Design | `doc/05_design/<feature>.md` | Phase 6 |
| System tests | `test/<mirrored-test-path>/<feature>_spec.spl` | Phase 8 |
| Generated spec docs | `doc/06_spec/<mirrored-test-path>/<feature>_spec.md` | Phase 8 |

**If ALL exist**, skip to Phase 8 (Implementation).

## Phases

### Phases 1-3: Research + Requirements
Skip if exist, otherwise do inline. See `research` skill for details.

### Phases 4-5: Plan + Design + Architecture
Skip if exist. See `design` skill for details.

### Phases 6-7: System Test + Doc Consistency
- Write SPipe BDD tests from design
- Verify doc cross-references are intact
- Keep generated/manual SPipe docs under `doc/06_spec/` mirrored from the
  executable `test/...` path after stripping the leading `test/` segment
- Never put executable `.spl` specs under `doc/06_spec`; verify
  `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0` before sync.
- Built-in matchers only (see `design` skill for list)
- For scenario-oriented specs, run the scenario manual update loop before
  implementation is considered ready: generate the doc, read it as a manual,
  improve steps/captures/visibility/helper names, and regenerate until the
  primary flow is manual-quality.
- If design introduced shared interface or manual setup/checker helper
  placeholders, implement them or keep them failing explicitly with
  `assert(false)` or `fail(...)`. Silent no-op helpers are not valid coverage.
- For broad lanes, preserve the cooperative review plan from design: lower-model
  sidecars such as Codex Spark, Claude Haiku, or Claude Sonnet must be merged or
  explicitly `N/A`, then a normal/highest-capability reviewer must accept broad
  findings, generated-manual quality, coverage claims, exclusions, and done
  marks before implementation handoff.
- When implementation changes workflow/tooling, evidence wrappers, generated
  specs, or verification contracts, update the matching `doc/07_guide`,
  `doc/06_spec`, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
  `.claude/agents/spipe/`, and `.gemini/commands/` instructions before
  `verify`; stale process docs are implementation work, not release cleanup.
- Do not mark the implementation goal complete if the changed workflow/tooling
  behavior is only proven by tests. The guide/skill/SPipe-agent doc freshness
  gate is part of completion, not a release follow-up.
- For `simple_context` or context-mode changes, keep the MCP/tooling guide and
  mirrored generated manuals current. SQL-backed context paths must document the
  `--sql`/`--db`/`--source-filter` CLI flags, MCP `source_filter`, the
  file-optional `sql=true` plus non-empty `query` contract, the embedded SQLite
  facade boundary, explicit absence statuses, and the required public-absence
  guard.
- Do not leave primary manual output dominated by raw test code. Executable
  SPipe should be folded detail; visible content should be scenario steps and
  typed evidence.
- For Simple Web or other HTML-backed GUI behavior, capture and check HTML
  visible text when possible, then use GUI screenshots as fallback evidence.
- When a GUI/web evidence wrapper claims live rendering, record structured
  browser event evidence too: focus, keyboard/input, pointer, and click delivery
  on visible controls. Static screenshots alone are visual evidence, not event
  handling evidence.
- Use `# @evidence-display: embed_tui`, `links`, or `embed_all` when generated
  evidence should differ from the default embedded TUI plus linked non-TUI
  artifacts.

### Phase 8: Implementation
- Implement in `src/**/<feature>.spl`
- Follow `/coding` rules strictly
- Reference: `doc/07_guide/quick_reference/syntax_quick_reference.md`
- For generated GPU backends, fail closed on unsupported MIR or artifact
  states. Do not emit target source containing placeholder unsupported-operation
  comments; return a typed diagnostic and add/refresh backend contract coverage.
- Shared-font work follows `$sp_dev` “Shared multilingual font work”: preserve
  `FontRenderer`, transient `FontRenderBatch`, `WebIR`, `DrawIrComposition`, and
  the plan-defined frozen SSpec vocabulary; keep secondary detail steps folded.
- Use short grammar deliberately:
  - Prefer expression-bodied functions for small pure helpers.
  - Prefer placeholder lambdas (`_`, `_1`, `_2`) and method references (`&:name`) only for single-expression transforms.
  - Prefer comprehensions for local map/filter construction.
  - Avoid `:=` until actual walrus-token parser/runtime tests pass; use `val`.
  - Avoid `|>` in native-targeted implementation unless the specific path passes with `SIMPLE_NO_STUB_FALLBACK=1`.

### Phases 9-10: Unit + Integration Tests
- 80%+ branch coverage target
- Write unit tests alongside implementation
- Write integration tests for cross-module interactions
- Add doctests for public API functions
- For short grammar changes, add interpreter and native coverage separately:
  - Interpreter specs may cover pipe-forward, composition, dynamic lambda dispatch, and no-paren DSL forms.
  - Native specs must avoid forms that only pass through codegen stub fallback.
  - Run native short-grammar tests with `SIMPLE_NO_STUB_FALLBACK=1` when checking support.

### Phases 11-13: Bug Reports + Duplication Check + Refactoring
- Run `bin/simple bug-add` for any discovered bugs
- Check for code duplication across `src/`
- Refactor: files > 800 lines must be split

### Phase 14: Full Test Suite
```bash
bin/simple test && bin/simple build lint
```

For compiler backend changes, add or refresh focused lint/spec coverage for
invalid target text such as `call nil`, `phi nil`, `getelementptr nil`, and raw
LLVM result type metadata. `LLVM001` must stay clean in LLVM emitter files. If
changing indirect-call/function-signature lowering, add a focused guard proving
`sig.return_type == nil` is not mapped through a backend type mapper.

### Phase 15: Verify + VCS Sync
- Run `verify` skill — must show STATUS: PASS
- For GUI/web/2D RenderDoc+Vulkan implementation work, use
  `scripts/setup/setup-gui-web-2d-vulkan-env.shs --check|--run|--renderdoc-simple|--renderdoc`
  as the canonical wrapper. For `--renderdoc-simple`, leave `RDOC_SIMPLE_BIN`
  unset in normal runs so the helper builds `src/compiler_rust/target/release/simple`
  with current `rt_renderdoc_*` externs.
  For browser diagnostics only, `RDOC_RENDERDOC_HOOK_CHILDREN=0` omits
  RenderDoc child-process hooking; record the result as blocker evidence unless
  the browser GPU-process `.rdc` still has valid `RDOC` magic.
  Do not treat Chromium `--in-process-gpu` as a valid Vulkan browser evidence
  shortcut on this Linux host; current Chrome/Electron reports or exhibits that
  Vulkan is unsupported/crashing in that mode.
- If `src/compiler/**`, `src/lib/**`, `src/app/mcp/**`, `src/app/simple_lsp_mcp/**`, or MCP packaging files changed, run:
  - `<runtime> check src/compiler`
  - `<runtime> check src/lib`
  - `<runtime> check src/app/mcp`
  - `<runtime> check src/app/simple_lsp_mcp`
  - `SIMPLE_LIB=src <runtime> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`
  - If publish/package flow changed:
  - `<runtime> native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_mcp_server`
  - `<runtime> native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/simple_lsp_mcp/main.spl --strip --output build/bootstrap/mcp-package/simple_lsp_mcp_server`
- VCS sync: `jj commit -m "feat: <feature description>"`

## Stub Prevention Gate

**STUB001 = HARD FAIL.** No `pass_todo` in final code.

Before declaring implementation complete, verify:
- No `pass_todo` anywhere in new/modified files
- No `pass_do_nothing("why no-op is correct")` / `pass_dn("why no-op is correct")` unless intentional
- Use `todo("what remains", "hint or issue")` only for explicit, tracked deferrals
- No hardcoded returns without logic
- No commented-out code blocks
- No empty function bodies

## Artifacts Produced

| Artifact | Path |
|----------|------|
| Implementation | `src/**/<feature>.spl` |
| Unit tests | `test/**/<feature>_spec.spl` |
| Integration tests | `test/**/<feature>_it_spec.spl` |
| Bug reports (if any) | Via `bin/simple bug-add` |

## Multi-LLM Collaboration

- If other LLMs produced research/design/tests, build on them
- Never overwrite existing artifacts — extend or improve
- Tag Codex-produced code with `# codex-impl` comment on module header if needed

## Rules

- All code in `.spl` — no Python, no Bash
- Generics use `<>` for type parameters — `Option<T>`, `Result<T, E>`; arrays use `[]` like `[i64]`
- Pattern binding: `if val` not `if let`
- Constructors: `Point(x: 3, y: 4)` not `.new()`
- `?` is operator only — never in names; use `.?` over `is_*` predicates
- NO inheritance — use composition, alias forwarding, traits, or mixins
- Use `Result<T, E>` + `?` for error handling (no try/catch/throw)
- Reserved keywords: `gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`, `pass_do_nothing`, `pass_dn`
- NEVER over-engineer — only make requested changes
- NEVER add unused code — delete completely
- NEVER convert TODO/FIXME to NOTE — implement or delete
- Production MCP or LSP wrappers must execute cached compiled artifacts, not raw source entrypoints
- Do not place full-tree scans or repeated file rereads in request handlers when a cache or index is viable
- When cached or indexed data depends on writable files, implement explicit invalidation on create, edit, move, delete, rename, template application, and bulk replace flows
- Add perf smoke coverage for startup and representative hot requests when changing performance-sensitive tooling
- For `simple run` script-startup work, preserve the driver fast path for `.shs`,
  `get_cli_args`, and `std.cli` scripts; verify
  `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` before claiming
  completion.
- After compiler/core/lib changes, verify MCP/LSP source-native startup before finishing the task; after packaging/release changes, verify isolated npm install startup too
- Short grammar is preferred where it is proven and readable; never normalize a failing compact form into a long workaround without either fixing it or recording a concrete bug/report.
