# Workaround Auto-Retire Feature Expert Skill

## Role

Own process knowledge for `bug-resolve --auto-retire` and the `check-dbs`
closure-bypass advisory (plan section 4 E-BUG-WR-004, section 5).

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- Design: `doc/05_design/workaround_retirement.md`
- Source: `src/app/bug/workaround_autoretire.spl` (pure), `src/app/bug/workaround_autoretire_cli.spl` (I/O),
  `src/app/bug_resolve/main.spl` (flag), `src/app/cli/check_dbs.spl` (advisory row `closure_gate_bypass`)
- Spec: `test/01_unit/app/bug/workaround_autoretire_spec.spl`
- Open gap: `doc/08_tracking/bug/workaround_retirement_bootstrap_advisory_hook_missing_2026-11-15.md`

## Current behaviour

- `--auto-retire` is default off. After a successful resolve it prints each live
  workaround site as `path:line`, edits nothing, and exits 1 while any remain or
  the index is incomplete/unavailable. The retirement module needs a root-fix commit,
  exact hunks and admitted proofs that index rows lack, so no source edit is applied.
- `check-dbs bugs` warns (advisory) when a fixed/closed bug still has a workaround.

## Update Rule

Update this file when the retirement transaction gains a producer of
`WorkaroundRetirementV1` records or a bootstrap hook lands.
