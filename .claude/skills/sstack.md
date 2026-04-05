# SStack Skill -- Superpowers + GSD + GStack Orchestrator

SStack is a full-lifecycle development pipeline that combines three frameworks:
- **Superpowers** -- BDD/TDD: spec-first, test-first, refactor
- **GSD** -- Sub-40% context budget per phase, fresh orchestrators, local state files
- **GStack** -- Specialized role agents, data flow pipeline, quality gates

## Invocation

```
/sstack <user request>
```

## How It Works

1. You (the orchestrator) run Phase 1 **inline** to refine the user request
2. For Phases 2-8, you spawn a **fresh Agent** per phase (GSD: fresh context)
3. Each agent reads `.sstack/<feature>/state.md`, does its work, writes updated state
4. After each agent returns, you read the state file and verify exit criteria
5. If exit criteria fail, re-run the phase (max 2 retries)

## Pipeline

| # | Phase | Role | Agent Definition |
|---|-------|------|-----------------|
| 1 | dev | Developer Lead | `.claude/agents/sstack/dev.md` |
| 2 | research | Analyst | `.claude/agents/sstack/research.md` |
| 3 | arch | Architect | `.claude/agents/sstack/arch.md` |
| 4 | spec | QA Lead | `.claude/agents/sstack/spec.md` |
| 5 | implement | Engineer | `.claude/agents/sstack/implement.md` |
| 6 | refactor | Tech Lead | `.claude/agents/sstack/refactor.md` |
| 7 | verify | QA | `.claude/agents/sstack/verify.md` |
| 8 | ship | Release Mgr | `.claude/agents/sstack/ship.md` |

## Orchestrator Procedure

### Step 0: Setup

1. Derive `<feature>` slug from the user request (lowercase, hyphens, e.g. `add-csv-export`)
2. Create directory `.sstack/<feature>/`
3. Create `.sstack/<feature>/state.md` with the initial template (see State File Format below)

### Step 1: Dev (inline -- do NOT spawn agent)

Run Phase 1 yourself:

1. Read the user request carefully
2. Categorize the task type: `feature`, `bug`, `todo`, or `code-quality`
3. Refine it into a clear, actionable, testable goal
4. Define 3-7 acceptance criteria (AC-1, AC-2, ...)
5. Write the task type, refined goal, and ACs into the state file under `## Task Type`, `## Refined Goal`, and `## Acceptance Criteria`
6. Mark `1-dev` as done in the phase checklist with today's date
7. Write a summary under `## Phase Outputs / ### 1-dev`
8. **Ask the user to confirm** the refined goal and ACs before proceeding

### Steps 2-8: Agent Phases

For each phase N (2 through 8):

1. **Read** `.sstack/<feature>/state.md` to get current state
2. **Read** the phase definitions from `.claude/skills/lib/sstack_phases.md` for phase N's entry/exit criteria
3. **Verify entry criteria** -- if the previous phase output is missing or incomplete, re-run the previous phase
4. **Spawn a fresh Agent** with this prompt:

```
Read .claude/agents/sstack/<phase-name>.md and follow its instructions.

State file: .sstack/<feature>/state.md
Feature: <feature>
Phase: <N>-<phase-name>

Read the state file, perform your role, then update the state file with:
- Your output summary under ## Phase Outputs / ### <N>-<phase-name>
- Mark your phase done in ## Phase Checklist
- Ensure exit criteria from .claude/skills/lib/sstack_phases.md are met
```

5. **After agent returns**, read `.sstack/<feature>/state.md`
6. **Verify exit criteria** for phase N (from sstack_phases.md)
7. If exit criteria fail: re-run the agent (max 2 retries), then escalate to user
8. Proceed to next phase

### Completion

After Phase 8 (ship) succeeds:
1. Read the final state file
2. Report to the user: refined goal, all ACs checked, summary of each phase output
3. Note any ACs that were not fully met

## State File Format

Create `.sstack/<feature>/state.md` with this template:

```markdown
# SStack State: <feature>

## User Request
> <original user request verbatim>

## Refined Goal
> <refined user request -- clear, actionable, testable>

## Acceptance Criteria
- [ ] AC-1: ...
- [ ] AC-2: ...
- [ ] AC-3: ...

## Phase Checklist
- [ ] 1-dev (Developer Lead)
- [ ] 2-research (Analyst)
- [ ] 3-arch (Architect)
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
<pending>

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
```

## GSD Budget Rule

Each agent phase must stay under **40% context window usage**. The orchestrator (you) should:
- Keep your own context lean -- delegate, do not accumulate
- Never paste full file contents into agent prompts; point agents to file paths
- If a phase is too large, split it into sub-phases within the same agent call

## Quality Gates

Between every phase transition, verify:
1. State file has the phase marked done with a date
2. Phase output section is non-empty and substantive
3. Exit criteria from `sstack_phases.md` are satisfied
4. No regression -- previous phase outputs are still intact in the state file

## Autonomous Mode

SStack can run autonomously via `scripts/sstack-orchestrator.sh`.
- Reads tasks from `.sstack/TASKS.md`
- Runs full pipeline for each task
- Monitor: `scripts/sstack-monitor.sh`
- Status: `.agent/STATUS.json`

## Language Dispatch

The orchestrator detects the target language from:
1. File extensions in the task description
2. Project structure (Cargo.toml → Rust, package.json → TypeScript, etc.)
3. Explicit `[lang:rust]` tag in task

Language agents: `.claude/agents/lang/<lang>.md`
Supported: simple, c_cpp, rust, python, typescript, go

When spawning Phase 5 (implement) or Phase 6 (refactor), include:
"Read .claude/agents/lang/<detected_lang>.md for language-specific rules"

## Integration with Existing Skills

SStack agents may invoke existing skills internally:
- Phase 2 (research): may use `/research` patterns
- Phase 4 (spec): may use `/sspec` for test structure
- Phase 5 (implement): may use `/coding` rules
- Phase 6 (refactor): may use `/refactor` checklist
- Phase 7 (verify): may use `/verify` checklist
- Phase 8 (ship): may use `/sync` for VCS and `/release` for versioning
