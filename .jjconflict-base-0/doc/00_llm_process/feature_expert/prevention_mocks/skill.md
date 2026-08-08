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
- Source (landed, unit U1): `src/lib/nogc_sync_mut/src/testing/mock/prevention.spl`
  (`ForbiddenCallGuard`, `check_guards`).
- Source (landed, unit U2): `src/lib/nogc_sync_mut/spec.spl`
  (`prevent`/`prevent_at_most`/`prevent_file` DSL — immediate-check
  semantics, not the originally-planned deferred-arming design; see
  `doc/08_tracking/bug/prevention_mock_deferred_arming_impossible_2026-08-07.md`).
- Spec (landed, unit U3): `test/01_unit/lib/std/testing/prevention_mock_spec.spl`.
- Adoption specs (landed, unit U5): `test/01_unit/compiler/di/di_lock_spec.spl`,
  `test/01_unit/app/devhub/adapter_bitbucket_spec.spl`,
  `test/01_unit/lib/common/mock_verification_spec.spl`.

## Status (2026-08-07)

- **All five units (U1-U5) are landed.** `ForbiddenCallGuard`/`check_guards`
  exist at `src/lib/nogc_sync_mut/src/testing/mock/prevention.spl`; `prevent`/
  `prevent_at_most`/`prevent_file` exist in `src/lib/nogc_sync_mut/spec.spl`
  and check IMMEDIATELY against the mock's current state at the call site
  (deferred "arm early, auto-check at end of `_execute_it`" was attempted
  and found impossible under this interpreter — a class instance stored in
  an array/field/closure is copied by value; full repro in
  `doc/08_tracking/bug/prevention_mock_deferred_arming_impossible_2026-08-07.md`).
  `prevent_file` is consequently a documented alias for `prevent`, not true
  auto-checked file scope.
- Directory-wide scope remains genuinely unspecifiable with the current
  test-runner architecture — same root cause as file-scope above
  (module-level spec state does not persist across `it` examples). Convention
  (`_prevention.spl` helper, opt-in) documented in the guide; gap tracked in
  the tracking record above.
- The guide (`doc/07_guide/infra/testing/prevention_mocks.md`) and
  `.claude/skills/spipe.md` § "Prevention mocks" carry the same landed-DSL,
  immediate-check framing for agents reading those files directly.

## Scope verdicts (from the plan)

| Scope | Specifiable? | Mechanism |
|-------|-------------|-----------|
| per-test (`it`) | YES (landed) | `prevent(mockfn, reason)` called AFTER the code under test; checks immediately, same-mechanism-as-`expect` |
| per-file | Partial (landed as an alias) | `prevent_file(mockfn, reason)` behaves exactly like `prevent()` — call it explicitly in every example (or `before_each`/`after_each`) to approximate file-wide coverage; true auto-checked file scope is NOT achievable (module-level state does not persist across `it` examples) |
| directory-wide | NO | No per-directory test-runner config/fixture hook exists; convention (`_prevention.spl` helper, opt-in) documented instead — see tracking record above |

## Gotchas

1. **The manual `verify_called(m, 0)` idiom still works and is still
   fail-open** (nothing auto-checks it) — prefer the `prevent()` DSL, which
   fails loudly by design. `mock_verification_spec.spl` dogfoods the manual
   form in both directions (0 calls → true, 1 call → false) as a regression
   guard on the idiom itself.
2. **No call interception.** A prevention mock only observes calls routed
   through it by composition/DI. It cannot see a direct `rt_file_write_text`
   or a raw socket call unless the dependency is injected at that seam, or an
   env-level identity probe (`src/lib/nogc_sync_mut/engine_probe.spl`) is
   used instead for engine-identity-class checks. `adapter_bitbucket_spec.spl`
   documents a case with no fetcher-injection point at all — the guard there
   records the invariant rather than intercepting a real call.
3. **`VerificationResult` fields are `passed: bool` / `error_message: text`**
   (built via `.success()` / `.failure(message)`,
   `src/lib/nogc_sync_mut/src/testing/mock/builder.spl:173-190`) — not
   `ok`/`message`. `ForbiddenCallGuard.check()` matches these exact field
   names.
4. **`find_config_file` walks cwd-relative current/parent/grandparent, not
   per-spec-directory** (`src/lib/nogc_sync_mut/test_runner/test_config.spl:297-302`)
   — this is the concrete reason directory-wide scope has no runner hook to
   attach to.
5. **Call `prevent`/`prevent_at_most`/`prevent_file` AFTER the code under
   test has run, never at the top of the `it` body** — see gotcha 1 in the
   guide's ordering-contract section; violating this silently makes the
   guard permanently green regardless of what actually happened.
6. **Import explicitly, fully-qualified**:
   `use std.nogc_sync_mut.spec.{prevent, prevent_at_most, prevent_file}`.
   `use std.spec.*` does not reliably resolve every `pub fn` in `spec.spl`
   (Defect 3 in the bug doc above) — a pre-existing wildcard-import gap, not
   specific to this DSL.
7. **A guard wired to a mock no code path can reach is vacuous, not
   evidence** — always sabotage-verify a new adoption (force the call, or
   lower an `at_most` budget below the real count) before trusting it; see
   "Don't land a guard you can't drive red" in the guide.

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
