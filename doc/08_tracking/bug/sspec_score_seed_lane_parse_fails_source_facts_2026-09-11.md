# sspec-score-seed-lane.shs fails on this host: seed parser rejects a transitive import (2026-09-11)

**Status:** OPEN (unverified 2026-09-12)

`sh scripts/check/sspec-score-seed-lane.shs <spec>` errors on every spec on
this host (`.claude/worktrees/agent-a786cf790505813ca`, macOS aarch64):

```
error: compile failed: parse: in ".../src/compiler/10.frontend/core/source_facts.spl":
Unexpected token: expected expression, found Indent
ERROR — nothing was checked (seed run rc=1, scored=0; see build/nb/seed_lane.<pid>/run.log)
```

## Root cause

The script reshapes only the five `src/app/sspec_maintain/{model,rules,score,
source_facts,analyzer}.spl` modules (plus `registry`) for the seed's older
grammar (`sspec-score-seed-lane.shs:7,147,188`). One of these (or a sibling it
imports) now transitively pulls in `src/compiler/10.frontend/core/source_facts.spl`
— a DIFFERENT file, unrelated to `sspec_maintain`'s own `source_facts.spl` —
which the seed's parser cannot read (`Unexpected token: expected expression,
found Indent`). That file is not in the script's reshape list, so it reaches
the seed unmodified.

## Seed identity used

```
bin/release/aarch64-apple-darwin/simple_seed   Jul 25 13:12:54 2026 (stale)
```

No fresher seed was available in this worktree; copying the seed binary from
the main checkout (`/Users/ormastes/simple/bin/release/aarch64-apple-darwin/simple_seed`)
did not change the mtime/result — same failure.

## Impact

Every `sh scripts/check/sspec-score-seed-lane.shs <spec>` invocation on this
host returns `ERROR — nothing was checked`, regardless of the spec's actual
content or quality. The Job 1 scoring task (score 9 new specs landed
2026-09-11 to GATE >= 80) could not get a numeric GATE score from this tool.
Fallback used: manual checklist verification against
`.claude/skills/spipe/SKILL.md` § "Scoring 90+" (grep for `step(`, `# @req`,
`# @capture(`, `## Purpose and audience`, `@manual_section` per `it` block),
with minimal additive edits to close gaps — never weakening any assertion.

## Unblock condition

Either (a) extend `sspec-score-seed-lane.shs`'s reshape list to also cover
`src/compiler/10.frontend/core/source_facts.spl` (or whatever module actually
pulls it in transitively — needs a real import trace, not guessed), or (b)
deploy a current self-hosted `bin/release/<triple>/simple` on this host so the
scorer can run via `simple sspec-maintain scan <spec>` directly instead of the
seed-lane workaround.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
