# Review Loop — Codex-First Bot Reviewer (Claude Fallback)

## Role

Sub-agent invoked by `review_loop.md` (L2 only — L1 is opportunistic
single-pass; L3 waits on humans). Produces a single bot-reviewer
verdict for a PR diff: `approve | request-changes | comment`.

Codex is preferred (cheaper, faster, separate token); Claude
general-purpose is the fallback when Codex is unavailable, rate-limited,
or returns a non-decisive `comment`.

## Inputs

- `PR_NUMBER` — pull-request number
- `TARGET` — `gh` | `bb`
- `BRANCH` — head branch
- `PR_DIFF` — diff text (caller pre-fetches via
  `gh pr diff ${PR_NUMBER}` or the bb adapter equivalent)
- `PR_BODY` — PR description (for context)

## Outputs (echoed as JSON to stdout)

```json
{
  "verdict": "approve|request-changes|comment",
  "approver": "codex|claude",
  "verdict_source": "codex:rescue|claude:general-purpose",
  "reasoning": "1-3 sentence summary",
  "inline_comments": [
    {"path": "src/foo.spl", "line": 42, "body": "..."}
  ]
}
```

`inline_comments` is empty for `approve`.

## Procedure

### 1. Probe Codex Availability

Invoke the `/codex:setup` skill and read its readiness output (the
skill description: "Check whether the local Codex CLI is ready and
optionally toggle the stop-time review gate" — readiness check is
its default mode):

```
/codex:setup
```

Parse the output for one of: `ready` | `unavailable` |
`rate-limited` | `not-configured`. If the skill output format
differs in your local install, treat any non-`ready` token as
"unavailable":

```bash
CODEX_OUTPUT=$(invoke_skill "codex:setup")
if echo "$CODEX_OUTPUT" | grep -qi 'ready'; then
  CODEX_AVAILABLE=true
else
  CODEX_AVAILABLE=false
fi
```

### 2. Dispatch to Codex (if available)

If `CODEX_AVAILABLE=true`: spawn the `codex:rescue` agent with the
review prompt:

```
Prompt to codex:rescue:
  You are a bot code-reviewer. Read the PR diff and PR body below.
  Decide ONE of:
    - approve          (no blocking issues)
    - request-changes  (must-fix issues — provide inline comments)
    - comment          (worth flagging but not blocking)
  Return STRICT JSON matching the schema in
  agents/review_loop_codex_first.md §Outputs.
  Diff:
  <PR_DIFF>
  Body:
  <PR_BODY>
```

Capture the JSON. Validate `verdict ∈ {approve, request-changes, comment}`.

- On JSON parse failure or schema mismatch: treat as `comment` and
  fall through to Claude.
- On agent-level failure (timeout, exec error): fall through to Claude.

If `verdict == approve` or `verdict == request-changes`: return
immediately with `approver=codex`, `verdict_source=codex:rescue`.

If `verdict == comment`: per the arch doc bot-reviewer rule, fall
through to Claude — Codex's `comment` verdict is non-decisive and we
want a second opinion before posting.

### 3. Fallback to Claude General-Purpose

Spawn a fresh Claude general-purpose agent (sub-agent, sonnet-class)
with the same prompt as Codex received, augmented with:

```
The Codex bot returned a non-decisive verdict (or was unavailable).
You are the fallback reviewer. Same JSON schema. Be decisive.
```

Capture JSON, validate, return with `approver=claude`,
`verdict_source=claude:general-purpose`.

If Claude also returns `comment`: that's the final verdict. The
caller (`review_loop.md` Step 5) will post inline comments and NOT
flip the merge gate.

### 4. Audit Trail

The returned JSON's `approver` + `verdict_source` are written into
the PR `state.json` by the caller (see `review_loop.md` §Audit Trail).
The PR UI separately shows the token-principal (the bot account that
owns the gh/bb token used to POST comments and approves). Together
these give: WHICH agent decided, WHICH bot account acted.

## Error Handling

| Condition                      | Action                                  |
|--------------------------------|-----------------------------------------|
| Codex not configured           | Skip Codex; go straight to Claude       |
| Codex rate-limited             | Skip Codex; go straight to Claude       |
| Codex JSON parse fail          | Log; fall through to Claude             |
| Codex returns `comment`        | Fall through to Claude                  |
| Claude exec failure            | Return verdict=`comment`, reasoning=    |
|                                | "Both reviewers failed; manual review   |
|                                | required" — caller treats as no-op      |

The caller (`review_loop.md`) MUST treat repeated bot-failure cycles
as a soft block: after 3 consecutive failures, set
`status=blocked` and cancel the schedule. The bot-reviewer must
NEVER tight-loop.

## Context Budget

Sub-30%. Each invocation: load PR diff (capped at 8000 lines —
truncate with marker), PR body, this skill file. No project source
unless explicitly referenced by an inline comment thread.
