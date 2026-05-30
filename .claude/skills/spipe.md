---
name: spipe
description: SPipe Skill — Simple Pipe (spec → test → report). BDD test writing, matchers, file structure, doc generation. Use when writing or editing `*_spec.spl` test files, debugging matcher failures, or scaffolding from `.claude/templates/spipe_template.spl`. Renamed from `sspec` on 2026-04-26.
---

# SPipe — Simple Pipe (spec → test → report)

The SPipe dev entrypoint lives at:

**[.claude/agents/spipe/dev.md](../agents/spipe/dev.md)**

Codex routes SPipe development work through `$sp_dev`:

**[.codex/skills/sp_dev/SKILL.md](../../.codex/skills/sp_dev/SKILL.md)**

Check or install that wiring with:

```bash
sh scripts/install-spipe-dev-command.shs --check
sh scripts/install-spipe-dev-command.shs --apply
```

## Quick references in the same directory

- [`.claude/agents/spipe/research.md`](../agents/spipe/research.md) — SPipe research phase
- [`.claude/agents/spipe/spec.md`](../agents/spipe/spec.md) — SPipe spec phase
- [`.claude/agents/spipe/implement.md`](../agents/spipe/implement.md) — SPipe implementation phase
- [`.claude/agents/spipe/verify.md`](../agents/spipe/verify.md) — SPipe verification phase
- [`.claude/skills/lib/spipe_phases.md`](lib/spipe_phases.md) — phase map
- [`doc/07_guide/testing/sspec_scenario_manual.md`](../../doc/07_guide/testing/sspec_scenario_manual.md) — scenario manual, capture, inline/previous scenario, and environmental-test guidance

## Scenario Manual Quality

SPipe specs are executable tests and generated manuals. For user-facing,
operator-facing, MCP/tooling, UI, protocol, hardware, system, and environmental
tests, generated `doc/06_spec/...` must read like a scenario manual:

- primary flows visible as ordered steps;
- `@inline` setup hidden as standalone content and expanded through `@prev` or
  `@include`;
- capture evidence attached under the step that caused it;
- advanced/edge/matrix/stress details folded or skipped by policy;
- executable SPipe folded below the manual.

Run `bin/simple spipe-docgen <spec> --output doc/06_spec` and revise the spec
until the generated manual is usable without opening the source.

## Template

```
cp .claude/templates/spipe_template.spl test/my_spec.spl
```

## Run

```
bin/simple test path/to/my_spec.spl
```
