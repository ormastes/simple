# SStack Dev Skill — Phase 1: Developer Lead

**Trigger:** `/sstack-dev` or when a user request needs goal refinement before implementation.

## What This Skill Does

Analyzes a task (feature/bug/todo/quality), refines it into a clear, actionable, testable goal with numbered acceptance criteria. Produces the initial `.sstack/<feature>/state.md` file that all subsequent SStack phases consume.

## When to Use

- A user provides a feature request, bug report, todo item, or code-quality improvement
- The request is vague and needs decomposition into testable criteria
- Starting a new SStack pipeline run

## Workflow

1. Read the user's raw request
2. Categorize the task type: `feature`, `bug`, `todo`, or `code-quality`
3. If ambiguous, ask up to 3 clarifying questions before proceeding
4. Decompose into a single refined goal statement (one sentence, specific, no weasel words)
5. Write numbered acceptance criteria (AC-1, AC-2, ...) — each independently testable
6. Create `.sstack/<feature>/state.md`

## Boundaries (Boil a Small Lake)

- ONLY goal refinement, task categorization, and acceptance criteria
- Do NOT research code, sketch architecture, or write specs
- Do NOT open source files
- Context budget: sub-40%

## Entry Criteria

- User has provided a raw request (text, issue link, or conversation excerpt)

## Exit Criteria

- `.sstack/<feature>/state.md` exists with:
  - `## Task Type` — one of: `feature`, `bug`, `todo`, `code-quality`
  - `## Refined Goal` — one sentence, specific
  - `## Acceptance Criteria` — numbered, each testable with pass/fail
  - `## Phase` set to `dev-done`
- The goal is specific enough that two developers would build the same thing
- Every AC answers "how do I know this is done?" with a concrete check

## State File Template

```markdown
# Feature: <short-name>

## Raw Request
<paste user's original request verbatim>

## Task Type
<feature | bug | todo | code-quality>

## Refined Goal
<one clear sentence — what, not how>

## Acceptance Criteria
- AC-1: <testable criterion>
- AC-2: <testable criterion>
- AC-3: ...

## Scope Exclusions
<anything explicitly out of scope>

## Phase
dev-done

## Log
- dev: Created state file with N acceptance criteria (type: <task-type>)
```

## Next Phase

Hand off to **sstack-research** (Phase 2: Analyst) once `Phase: dev-done` is set.
