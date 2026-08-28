# Ponytail — repo-local lazy-developer mode

The repo carries a full replacement for the user-level `ponytail` plugin, so the
plugin can be uninstalled. Three parts: a skill, a persistence hook layer, and a
real `simple_ponytail` MCP tool.

## 1. Skill (the prompt)

| Host | File |
|------|------|
| Claude Code | `.claude/skills/ponytail.md` (canonical) |
| Codex | `.codex/skills/ponytail/SKILL.md` |
| Agents | `.agents/skills/ponytail/SKILL.md` |
| Gemini | `.gemini/commands/ponytail.toml` |

The ladder (stop at the first rung that holds): 1 YAGNI → 2 Simple stdlib →
3 native/platform feature (compiler pass, existing `scripts/check` gate, lint
rule, SDN schema, DB constraint) → 4 already-installed dependency (typed std
alias over direct `rt_*`, existing `src/app` module) → 5 one line → 6 minimum
`.spl`/`.shs`. Rules, output pattern (`[code] → skipped: [X], add when [Y]`),
intensity table (lite/full/ultra) and the "when NOT to be lazy" guardrails are
in the skill body. Repo rules (no inheritance, `<>` generics, MDSOC+) always win
over laziness.

## 2. Persistence across turns

State: `.simple/ponytail.level` (gitignored via `.simple/`). Contents: `lite`,
`full`, `ultra` or `off`. Missing file means `full`.

Wired in `.claude/settings.json` → `hooks`:

| Event | Script | Behaviour |
|-------|--------|-----------|
| `SessionStart` (matcher `startup\|resume\|clear\|compact`) | `.claude/hooks/ponytail-session-start.shs` | prints `PONYTAIL MODE ACTIVE — level: <x>` + the skill body; prints nothing when `off` |
| `UserPromptSubmit` | `.claude/hooks/ponytail-prompt.shs` | `/ponytail lite\|full\|ultra` → writes level; bare `/ponytail` → `full`; "stop ponytail" / "normal mode" / `/ponytail off` → `off`; prints `PONYTAIL MODE CHANGED — level: <x>` / `PONYTAIL MODE OFF` |

Both scripts honour `PONYTAIL_LEVEL_FILE` (and the start hook
`PONYTAIL_SKILL_FILE`) so they can be tested without touching the real state:

```bash
sh .claude/hooks/ponytail-session-start.shs --selftest   # Results: 6 passed, 0 failed
sh .claude/hooks/ponytail-prompt.shs --selftest          # Results: 7 passed, 0 failed
PONYTAIL_LEVEL_FILE=/tmp/lvl sh .claude/hooks/ponytail-session-start.shs | head -1
```

The `compact` matcher is what makes the mode survive context compaction — the
banner and skill are re-injected after every compaction.

## 3. `simple_ponytail` MCP tool

Lazy-loaded in `src/app/mcp/main_lazy_query_tools.spl` (`handle_simple_ponytail`),
schema in `src/app/mcp/main_static_tools.spl` (`_mcp_static_ponytail_props`).
Heuristics live in the stdlib, `src/lib/common/ponytail/ladder.spl`, and are pure
text — no I/O, no seed subprocess, so no banner leakage.

| Param | Values |
|-------|--------|
| `file` | path; optional when `diff` is given |
| `diff` | unified diff text; only **added** lines yield findings, line numbers are new-file numbers |
| `mode` | `audit`/`review` (legacy counters + `ladder findings:` section, default), `simplification`/`simplify`, `ladder` (findings only) |
| `level` | `lite` (weight-3 findings only), `full` (default, weight ≥2), `ultra` (all) |
| `format` | `text` (default), `markdown`, `json` |
| `lint` | `true` appends the first 20 lines of `simple lint <file>` (opt-in: ~12s startup) |

Finding line format: `L<line> rung<k> <kind>: <what> -> <fix>`.

| kind | rung | weight | heuristic |
|------|------|--------|-----------|
| `unused` | 1 | 3 (`_private`) / 1 (public) | `fn` name occurs once in the file |
| `placeholder` | 1 | 3 | `pass_todo` / `expect(true).to_equal(true)` |
| `todo` | 1 | 2 | `TODO`/`FIXME` with no `ponytail:` ceiling |
| `stdlib` | 2 | 2 | fn named like a text/array helper (`*_split`, `*line_count`, `*_trim`, …) |
| `direct-rt` | 4 | 2 | direct `rt_*(...)` call (typed std alias exists) |
| `one-line` | 5 | 2 | `return true` / `else:` / `return false` |
| `single-impl` | 6 | 2 | `trait`/`interface` with ≤1 `impl … for X:` in file |
| `factory-for-one` | 6 | 2 | `class *Factory` / `class *Builder` |
| `config-for-constant` | 6 | 2 | defaulted field of `*Config`/`*Options`/`*Settings` never read |
| `missing-ceiling` | 6 | 2 | nested loop, `sleep(`, `unsafe`, lock without `# ponytail:` within 2 lines above |
| `nesting` | 6 | 2 | indent ≥ 24 columns |
| `long-fn` | 6 | 2 (>60) / 1 (>30) | code lines per function |
| `duplicate` | 6 | 2 | a >40-char code line repeated ≥3 times |

Per kind at most 5 lines are shown, then `(<kind>: N more not shown)`. Findings
below the level threshold are counted as `hidden at level <x>`.

Suppress a finding by adding the ceiling comment it asks for, e.g.
`# ponytail: O(n^2) scan, index when n grows` on the line above.

## Tests

`bin/simple test test/01_unit/app/mcp/ponytail_spec.spl` — scanner fixtures per
kind, level filtering, diff scoping, MCP dispatch (`file`, `diff`, invalid
`level`), and the two hook self-tests via `process_run_timeout`.

Legacy counters (`placeholder markers:` etc.) remain in
`src/lib/common/ponytail/audit.spl` and are still asserted by
`test/01_unit/app/tooling/ponytail_audit_spec.spl` and the
`check-llm-tooling-context-ponytail-full-replacement.shs` gate.
