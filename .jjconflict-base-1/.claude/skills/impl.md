# Impl Skill -- 15-Phase Implementation Workflow

## Cooperative Phase
**Implementation phase** — runs after design is complete (Steps 1-5 or solo design).
- Any model can run implementation (Claude primary, Gemini/Codex secondary)
- Self-sufficient: if design artifacts missing, does design inline
- See: `doc/07_guide/app/llm/llm_cooperative_dev_phase.md`

**Self-sufficient.** If research, requirements, or design are missing, do them first (phases 1-5 handle this). Does not depend on Codex or Gemini having run prior steps.

## Prerequisites Check

Before starting, check what exists — missing artifacts are created in phases 1-5:

| Artifact | Path | Phase |
|----------|------|-------|
| Research | `doc/01_research/<domain>/<topic>/<feature>.md` | 1-2 |
| Requirements | `doc/02_requirements/<domain>/<topic>/<feature>.md` | 1-3 |
| Architecture | `doc/04_architecture/<domain>/<topic>/<feature>.md` | 4 |
| Design | `doc/05_design/<domain>/<topic>/<feature>.md` | 4 |
| System tests | `test/03_system/app/<app_name>/feature/<feature>_spec.spl` | 6 |
| Generated spec docs | `doc/06_spec/03_system/app/<app_name>/feature/<feature>_spec.md` | 6 |

**If ALL artifacts exist** (from prior `/research_claude` + `/research_codex` + `/design_gemini` + `/design_codex` + `/design_claude`), skip to Phase 6.

**Agent teams:** This workflow uses opus agent teams. See `/agents` skill for team patterns.

## Phase Overview

| # | Phase | Agent | Output |
|---|-------|-------|--------|
| 1 | Requirements | main | `doc/02_requirements/<domain>/<topic>/<feature>.md` |
| 2 | Research | research-team | `doc/01_research/<domain>/<topic>/<feature>.md` |
| 3 | Req Update | main | Updated requirement doc |
| 4 | Plan + Design | design-team | `doc/03_plan/agent_tasks/<feature>.md`, `doc/05_design/<domain>/<topic>/<feature>.md` |
| 5 | Model Selection | main | Task-to-model assignment |
| 6 | System Test | test-agent | `test/03_system/app/<app_name>/feature/<feature>_spec.spl` |
| 7 | Doc Consistency | review-agent | Cross-ref validation |
| 8 | Implementation | code-team | `src/**/<feature>.spl` |
| 9 | Unit + IT Tests | test-agent | 80%+ branch coverage |
| 10 | Doctest | code-agent | `"""..."""` sdoctest for public fns |
| 11 | Bug Reports | review-agent | `doc/08_tracking/bug/<feature>_limitations.md` |
| 12 | Duplication Check | review-agent | jscpd + semantic + stub scan |
| 13 | Refactoring | code-agent | Files >800 lines split |
| 14 | Full Test Suite | test-agent | All tests pass |
| 15 | VCS Sync | main | `/git-jj-sync` + completion report |

## Agent Teams

```
research-team:  explore -> docs          (sequential)
design-team:    explore -> code -> docs  (sequential)
code-team:      code -> test             (sequential)
review-team:    explore -> docs          (sequential)
```

## Phase Details

### Phase 1-3: Requirements + Research
**Preferred:** Run `/research_claude` (Step 1) then `/research_codex` (Step 2) before starting impl.
**Skip if artifacts exist.** Otherwise do them inline:
1. Local research: search `src/` and `doc/` for related code and prior work
2. Domain research: web search for external knowledge
3. Generate requirement options, ask user to select
4. Write final: `doc/02_requirements/<domain>/<topic>/<feature>.md` and `doc/02_requirements/<domain>/<topic>/<feature>_nfr.md`

### Phase 4-5: Plan + Design + Model Selection
**Preferred:** Run `/design_gemini` (Step 3) -> `/design_codex` (Step 4) -> `/design_claude` (Step 5) before starting impl.
**Skip if artifacts exist.** Otherwise do them inline:
1. Architecture: `doc/04_architecture/<domain>/<topic>/<feature>.md`
2. Detail design: `doc/05_design/<domain>/<topic>/<feature>.md`
3. Agent tasks: `doc/03_plan/agent_tasks/<feature>.md`
4. UI design (if applicable): `doc/05_design/ui/<topic>/<feature>_tui.md`, `_gui.md`

### Phase 6-7: System Test + Doc Consistency
1. Create `test/03_system/app/<app_name>/feature/<feature>_spec.spl` (SPipe BDD, fail-first). See `/spipe`
   - **REQUIRED:** Add `# @cover src/path/to/impl.spl <pct>%` pointing to last-layer component
2. Cross-ref: bidirectional links, consistent terminology, REQ-ID tracing
3. If design introduced shared interface or manual setup/checker helper
   placeholders, implement them or keep them failing explicitly with
   `assert(false)` or `fail(...)`. Silent no-op helpers are not valid coverage.

### Phase 8: Implementation
1. Implement in `src/**/<feature>.spl`, follow `/coding` rules
2. Shared-font work follows `.codex/skills/sp_dev/SKILL.md` “Shared multilingual font work”:
   preserve `FontRenderer`, transient `FontRenderBatch`, `WebIR`,
   `DrawIrComposition`, and the plan-defined frozen SSpec vocabulary; keep
   secondary detail steps folded.
3. **Stub Prevention Gate** (mandatory):
   - `bin/simple lint <touched .spl files>`
   - `bin/simple query workspace-symbols --query pass_todo` to find stubs
   - No function ignoring all params (STUB001 = hard fail)
   - Design/spec placeholders must fail explicitly with `assert(false)` or
     `fail(...)`; final implementation must not contain `pass_todo`

### Phase 9-10: Tests + Doctest
1. Unit + integration tests, target 80%+ branch coverage
2. Add sdoctest to every public fn: `""" sdoctest: expect(...).to_equal(...) """`

### Phase 11-13: Bug Reports + Duplication + Refactoring
1. Document workarounds in `doc/08_tracking/bug/<feature>_limitations.md`
2. Duplication: `bin/simple duplicate-check <dir>` (token + cosine + semantic)
3. Stub scan: verify pass_todo reasons, detect identity-returns (STUB001 = hard fail -> loop to Phase 8)
4. Split files >800 lines
5. Run `/refactor` skill for comprehensive code quality check.

### Phase 14-15: Full Test Suite + VCS Sync
```bash
bin/simple test test --whole --mode=interpreter
bin/simple lint <touched .spl files>
bin/simple duplicate-check <owned-dir> --mode token --min-lines 5
```
Run `/verify` (Claude) for production readiness verification.

All pass -> `/git-jj-sync` -> `doc/09_report/<feature>_complete_<date>.md`
Add/update guide docs in `doc/07_guide/` if needed.
Before verify/sync, workflow, tool-contract, evidence-wrapper, or
verification-contract changes must refresh matching `doc/07_guide`,
`doc/06_spec`, `.codex/skills/`, `.agents/skills/`, `.claude/skills/`,
`.claude/agents/spipe/`, and `.gemini/commands/` process docs.
For `simple_context` or context-mode changes, keep the MCP/tooling guide and
mirrored generated manuals current. SQL-backed context paths must document
`--sql`/`--db`/`--source-filter`, MCP `source_filter`, the file-optional
`sql=true` plus non-empty `query` contract, the embedded SQLite facade boundary,
explicit absence statuses, and the public-absence guard.
For GUI/web/2D RenderDoc+Vulkan work, use
`scripts/setup/setup-gui-web-2d-vulkan-env.shs --check|--run|--renderdoc-simple|--renderdoc` as
the macOS top-level readiness/direct-run/capture wrapper. Keep Windows and
Linux out of the top-level completion claim until their platform runbooks are
added. Refresh the guide, SPipe skill, verify mirrors, Simple
Vulkan/Engine2D evidence, Chrome gate, Electron gate, and production GUI/web
parity evidence together.
Do not use browser `RDOC_RENDERDOC_HOOK_CHILDREN=0` or Chromium
`--in-process-gpu` as passing Linux RenderDoc evidence unless the run still
emits a valid browser GPU-process `.rdc` with `RDOC` magic and proves Vulkan is
active.

## Per-Agent Checks

- **code**: compile + tests + duplication + stub scan (STUB001 = hard fail)
- **test**: fail-first verification, coverage target met
- **review**: cross-ref consistency + stub scan on all new decls
- **main**: docs approved before moving phases, verify stub stats in completion report
- Production MCP or LSP wrappers must use cached compiled artifacts for normal execution
- Avoid full-tree scans and per-request subprocesses in hot request handlers unless explicitly designed and justified
- When adding caches or indexes tied to writable files, add invalidation on all relevant mutation paths
- Add perf smoke checks for startup and representative tool requests when touching performance-sensitive tooling
