# Feature Expert — `test_in_development_tag`

**Created:** 2026-08-23. Covers the `@tag:in-development` test/feature tag: its
semantics, its runner enforcement, its statistics surfaces, and — the part that
matters most — the policy boundary that keeps it from becoming a mute button.

## Role

Own process knowledge for one narrow idea: a test written *ahead of* its
implementation is honest work in progress, and must be visible as debt rather
than either (a) turning the whole suite red or (b) disappearing silently.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- Canonical guide: `doc/07_guide/infra/testing.md` § Tags and Filtering →
  `@tag:in-development`
- Agent-facing spec-writing process: `.claude/skills/spipe.md` §
  "`@tag:in-development` — the ONE legitimate way to ship an expected-to-fail spec"
- Runner layer: `doc/00_llm_process/layer_expert/test_runner/skill.md`
- Hardening plan §27: `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`

## The contract

| Property | Meaning |
|---|---|
| Marked | `# @tag:in-development` header comment, plus a MANDATORY `# Tracks: <TODO/bug/plan row>` line |
| Expected | FAIL — a red result is the normal state |
| Whole-suite run | SKIPPED (cannot turn `bin/simple test` red) |
| Summary | COUNTED — the count is a debt figure that is supposed to fall |
| Selection | `simple test --tag in-development` |

## Enforcement status — verify before you assert

Checked against `origin/main` @ `3ccf808f6f2`, 2026-08-23:

- **Exists:** `--tag <name>` filtering in the seed driver
  (`src/compiler_rust/driver/src/cli/test_runner/args.rs:24`; forwarded to the
  spec child at `execution.rs:923-925`); `--show-tags` (`execution.rs:911`);
  `@tag:qemu` substring scanning for the timeout budget (`execution.rs:95`).
- **Does NOT exist:** any `@tag:` parsing in the pure-Simple runner.
  `src/app/test_runner_new/test_runner_single.spl` parses exactly `# @di_test`
  (`:193`) and `# @exec_limit <N>` (`:209`). No skip, no count, no statistics
  surface, no `in-development` value anywhere in `src/`.

Consequence: a spec tagged today **still runs and still fails**. Any report or
doc that says otherwise is wrong. This repo has repeatedly shipped docs asserting
enforcement that did not exist (`.claude/rules/vcs.md` once claimed five guards
were wired when they were wired to nothing) — re-grep origin before claiming.

## Anti-use — the boundary that gives the tag its value

Never for: a **regression** (used to pass, now fails — fix or revert); an
**undiagnosed** failure (that is an unfiled bug); **environmental**
unavailability (use `skip(name, reason)` / `pending(name)`,
`src/lib/gc_async_mut/spec/__init__.spl:40-43`, or the host-aware
`skip:`/`blocked:` wording); getting a red suite green before a landing; or
keeping a spec for behaviour nobody intends to build (delete it).

One line: **in-development means the CODE is missing; everything else means the
TEST or the ENVIRONMENT is wrong.**

## Promotion

The moment it passes, delete the tag and the `Tracks:` line in the same commit as
the fix, and close the tracked row. A passing spec still tagged is a stale
ratchet — the count stops meaning anything, which is the failure mode this
feature exists to prevent.

## Artefacts the count must reach

`doc/08_tracking/test/test_result.md`, `doc/08_tracking/test/test_db.sdn`,
`doc/02_requirements/feature/feature.md`, and
`doc/02_requirements/feature/pending_feature.md` are regenerated on every test
run (see `.claude/rules/structure.md`). The in-development count belongs in the
first two; an in-development feature belongs in `pending_feature.md`, not
`feature.md`. Wiring that is the statistics lane's work, not this doc's claim.
