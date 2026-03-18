# Hooks, Skills & Tools — Implementation Plan

## Current Status

| Component | Status | Notes |
|-----------|--------|-------|
| Hook infrastructure | NEW | No hooks except Stop agent-loop-hook |
| Skill frontmatter | UPDATING | 22 skills need description field |
| mcp-failure-analysis | BROKEN | Command exists, no skill file |
| New skills (hook, verify-work, benchmark) | NEW | Need creation |
| Research doc | NEW | Consolidated analysis |

## Task Breakdown

### Priority 1 — Enforce CLAUDE.md Rules (HIGH VALUE, LOW RISK)

| # | Task | Difficulty | Status |
|---|------|-----------|--------|
| 1 | Add frontmatter to 22 skills | Easy | Done |
| 2 | Fix mcp-failure-analysis command | Easy | Done |
| 3 | Create binary-guard.sh hook | Medium | Done |
| 4 | Create comment-replace-detect.sh hook | Medium | Done |
| 5 | Create auto-lint-warn.sh hook | Easy | Done |
| 6 | Create todo-check.sh hook | Easy | Done |

### Priority 2 — Quality Gates (MEDIUM RISK)

| # | Task | Difficulty | Status |
|---|------|-----------|--------|
| 7 | Create completion-guard.sh hook | Medium | Done |
| 8 | Create auto-checkpoint.sh hook | Easy | Done |
| 9 | Create pure-simple-guard.sh hook | Easy | Done |

### Priority 3 — Quality of Life (LOW RISK)

| # | Task | Difficulty | Status |
|---|------|-----------|--------|
| 10 | Create session-summary.sh hook | Easy | Done |
| 11 | Create hook.md skill | Easy | Done |
| 12 | Create verify-work.md skill | Easy | Done |
| 13 | Create benchmark.md skill | Easy | Done |
| 14 | Create command files | Easy | Done |
| 15 | Update settings.json | Medium | Done |
| 16 | Create research doc | Easy | Done |
| 17 | Create plan doc | Easy | Done |

## Design Decisions

| Question | Decision | Rationale |
|----------|----------|-----------|
| Individual scripts vs inline | Individual files | Testable, clean diffs, easy toggle |
| Block vs warn | Only binary-guard blocks | Low false-positive requirement |
| Auto-lint: run per-edit? | No — reminder only | Latency concern |
| Block session end? | No — warn only | User frustration concern |
| Auto-checkpoint: commit or describe? | Describe only | Less invasive with jj |

## Verification

1. Hook scripts: test with echo JSON | bash script
2. Settings.json: validate with jq
3. Skill frontmatter: check head -5 of each file
4. New skills: invoke /hook, /verify-work, /benchmark
5. Docs: verify files exist
