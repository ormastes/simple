# Prevention Mocks Feature Expert

## Role

Own feature-specific process knowledge for **prevention mocks** — mocks whose
purpose is to FAIL a test when a forbidden call path is taken (real fs write
in a pure test, network in a unit test, DI mutation while locked, deprecated
API), at per-test, per-file, and directory-wide scope.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- Plan (all 5 units, design authority): [doc/03_plan/infra/testing/sspec_prevention_mock_plan_2026-08-07.md](../../../03_plan/infra/testing/sspec_prevention_mock_plan_2026-08-07.md)
- Guide: [doc/07_guide/infra/testing/prevention_mocks.md](../../../07_guide/infra/testing/prevention_mocks.md)
- Tracking record (directory-wide scope gap, U4): [doc/08_tracking/bug/sspec_no_dir_wide_prevention_scope_2026-08-07.md](../../../08_tracking/bug/sspec_no_dir_wide_prevention_scope_2026-08-07.md)
- Related policy guide (mock-creation ban, a different kind of prevention): [doc/07_guide/infra/security/mock_policy_system_test_ban.md](../../../07_guide/infra/security/mock_policy_system_test_ban.md)
- Layer expert: [layer_expert/test_runner](../../layer_expert/test_runner/skill.md)
- Source (existing mock library, used by prevention idiom today):
  `src/lib/nogc_sync_mut/src/testing/mock/builder.spl` (`MockFunction`,
  `VerificationResult`, `MockPolicy`), `mock/verification.spl`
  (`verify_called`, `verify_called_with`, `Matcher`, `CallAnalyzer`),
  `mock/spy.spl` (`Spy`).
- Source (planned, not yet landed as of 2026-08-07): `src/lib/nogc_sync_mut/src/testing/mock/prevention.spl`
  (`ForbiddenCallGuard`, `check_guards` — unit U1) and
  `src/lib/nogc_sync_mut/spec.spl` (`prevent`/`prevent_at_most`/`prevent_file`
  DSL — unit U2). Other `src/lib/*/spec.spl` (`gc_async_mut`, `gc_sync_mut`,
  `nogc_async_mut`) re-export from `nogc_sync_mut` and need the mirrored diff
  if they turn out to be full copies rather than re-exports (checked at U2
  time).
- Planned spec: `test/01_unit/lib/std/testing/prevention_mock_spec.spl` (U3).
- Planned adoption specs (U5): `test/01_unit/compiler/di/di_lock_spec.spl`,
  `test/01_unit/app/devhub/adapter_bitbucket_spec.spl`,
  `test/01_unit/lib/common/mock_verification_spec.spl`.

## Status (2026-08-07)

- **U4 (this entry, plus the guide and tracking record) is landed.**
  Doc-only: describes what exists today (the manual `verify_called(m, 0)`
  idiom, fail-open), what's planned (`prevent`/`prevent_file` DSL, U1-U3),
  and documents the directory-wide scope as genuinely unspecifiable with the
  current test-runner architecture.
- **U1 (`ForbiddenCallGuard`/`check_guards`), U2 (`prevent`/`prevent_file`
  DSL in `spec.spl`), U3 (spec + sabotage recipe), and U5 (adoption in 3
  specs) are NOT YET LANDED.** Verified 2026-08-07: no `prevention.spl` file
  under `src/lib/nogc_sync_mut/src/testing/mock/`, and no `prevent` symbol in
  `src/lib/nogc_sync_mut/spec.spl`.
- `.claude/skills/spipe.md` § "Prevention mocks" carries the same
  today-vs-planned framing for agents reading that skill file directly.

## Scope verdicts (from the plan)

| Scope | Specifiable? | Mechanism |
|-------|-------------|-----------|
| per-test (`it`) | YES (once U1+U2 land) | `prevent(...)` registered in `it`, auto-checked at end of `_execute_it` |
| per-file | YES (once U2 lands) | `prevent_file(...)` at spec top level; checked after every `it` |
| directory-wide | NO | No per-directory test-runner config/fixture hook exists; convention (`_prevention.spl` helper, opt-in) documented instead — see tracking record above |

## Gotchas

1. **The prevention idiom already exists manually and is fail-open.**
   `verify_called(m, 0)` asserted at the end of an `it` works today with zero
   new code — but nothing auto-checks it, so a forgotten assertion silently
   passes an example that took the forbidden path.
2. **No call interception.** A prevention mock (planned or manual) only
   observes calls routed through it by composition/DI. It cannot see a
   direct `rt_file_write_text` or a raw socket call unless the dependency is
   injected at that seam, or an env-level identity probe
   (`src/lib/nogc_sync_mut/engine_probe.spl`) is used instead for
   engine-identity-class checks.
3. **`VerificationResult` fields are `passed: bool` / `error_message: text`**
   (built via `.success()` / `.failure(message)`,
   `src/lib/nogc_sync_mut/src/testing/mock/builder.spl:173-190`) — not
   `ok`/`message`. Anyone implementing U1's `ForbiddenCallGuard.check()` must
   match these exact field names.
4. **`find_config_file` walks cwd-relative current/parent/grandparent, not
   per-spec-directory** (`src/lib/nogc_sync_mut/test_runner/test_config.spl:297-302`)
   — this is the concrete reason directory-wide scope has no runner hook to
   attach to.

## Update Rule

When the project process creates or changes research, requirements,
architecture, design, tests, implementation, verification, or release
artifacts for prevention mocks, update this skill with the new links and the
current handoff notes.

## Update Checklist

- Add links to new or changed requirements, architecture, design, plans,
  specs, and reports.
- Record affected layers and link their layer expert skills.
- Record implementation constraints, known blockers, and required
  verification commands.
- Update this file after each pipeline stage before handing off to the next
  stage.
- When U1-U3 land, update the "Status" section above and move their entries
  out of "planned, not yet landed."
