# Prevention Mocks

A **prevention mock** is a mock whose job is to *fail the test when a
forbidden call path is taken* — a real filesystem write inside a pure unit
test, a network call inside a unit test, a DI mutation while the container is
locked, a call to a deprecated API. This is the opposite purpose from a
normal stub/mock: a stub answers calls; a prevention mock exists to catch
calls that should never have happened.

This differs from `MockPolicy` / `MockMode` (see
`doc/07_guide/infra/security/mock_policy_system_test_ban.md`), which bans
mock *creation* itself in system tests. A prevention mock does the opposite:
it is a mock that is intentionally created and injected specifically so a
forbidden call becomes observable and fails the example.

## What exists today

The full pure-Simple mock library lives at
`src/lib/nogc_sync_mut/src/testing/` (facade: `mocking_core.spl`):

- `mock/builder.spl` — `MockFunction` (records calls via `record_call`),
  `MockBuilder.returns(...)`, `MockRegistry`, `VerificationResult`
  (`passed: bool`, `error_message: text`, built by `.success()` /
  `.failure(message)`), and `MockPolicy` / `mock_policy_init` /
  `mock_policy_disable` / `mock_policy_reset` / `mock_policy_allow_in_layer`.
- `mock/verification.spl` — `Matcher` (any/eq/gt/contains/predicate/...),
  `CallAnalyzer`, `verify_called(mockfn, times)` (line 128),
  `verify_called_with(mockfn, args)` (line 131), `Expectation.verify_all()`.
- `mock/spy.spl` — `Spy` (`method_called`, `method_call_count`,
  `total_calls`).

**The prevention idiom exists today, but it is manual and fail-open.** There
is no dedicated prevention API yet — you express "this must never be called"
by asserting `verify_called(m, 0)` at the end of the `it` body:

```simple
val m = MockFunction.new("legacy_write")
# ... exercise the code under test, injecting `m` at the seam ...
val result = verify_called(m, 0)
assert_true(result.passed)
```

Nothing auto-verifies this. If the assertion is forgotten, the example stays
green even if the forbidden call happened — the check is fail-open by
construction.

## Planned: `prevent` / `prevent_file` DSL

A first-class `prevent(mockfn, reason)` / `prevent_at_most(mockfn, n, reason)`
/ `prevent_file(mockfn, reason)` API, auto-checked at the end of every `it`,
is designed in
`doc/03_plan/infra/testing/sspec_prevention_mock_plan_2026-08-07.md` (units
U1-U3) but **not yet implemented** as of 2026-08-07 — `src/lib/nogc_sync_mut/spec.spl`
has no `prevent` symbol and
`src/lib/nogc_sync_mut/src/testing/mock/prevention.spl` does not exist yet.
When it lands, the two specifiable scopes will be:

- **Per-test (`it`):** `prevent(mockfn, reason)` called inside the `it` body;
  the guard is checked and cleared at the end of that one example.
- **Per-file:** `prevent_file(mockfn, reason)` called at the top of the spec
  file; the guard is checked after *every* example in that file and is not
  cleared between examples (reset the mock's own call log in `before_each` if
  per-example isolation is wanted).

Until U1-U3 land, use the manual `verify_called(m, 0)` idiom above.

## What prevention mocks cannot see

**There is no call interception.** A mock — prevention or otherwise — only
observes calls that are routed through it by composition/dependency
injection. It cannot see a direct `rt_file_write_text` call, a raw socket
call, or any other call that bypasses the mock entirely. To make a forbidden
call observable you must either:

- **Inject the mock at the seam** — pass the mock (or a fake wrapping it)
  wherever the real dependency would normally be consumed, so the call is
  routed through it, or
- **Use an env-level probe for engine identity** — `engine_probe.spl`
  (`src/lib/nogc_sync_mut/engine_probe.spl`) answers "which engine am I
  running under", which is a different, narrower kind of prevention (e.g.
  "this spec must never silently fall back to the interpreter").

A prevention mock is therefore evidence about the paths that were wired
through it, not a general guarantee that a forbidden operation never
happened anywhere in the process.

See also `doc/07_guide/infra/security/mock_policy_system_test_ban.md` for the
separate mock-creation-ban policy.

## Directory-wide scope: NOT specifiable today

The test runner has no per-directory configuration hook. It reads a single
repo-level `config/simple.test.sdn`
(`src/lib/nogc_sync_mut/test_runner/test_config.spl`,
`find_config_file` at line 297 searches only the current, parent, and
grandparent directories from the process's cwd — not per-spec-directory).
Spec discovery (`src/app/test_runner_new/`) has no shared-fixture-per-directory
mechanism either. A guard armed in one spec file has no way to apply itself
to every other spec file in the same directory automatically.

**Convention until runner support lands:** put a `_prevention.spl` helper in
the spec directory that exports a single function, e.g.:

```simple
# test/01_unit/some/dir/_prevention.spl
use std.spec.prevent_file
use std.testing.MockFunction

pub fn arm_dir_prevention():
    """Call this as the first line of every spec body in this directory."""
    val m = MockFunction.new("forbidden_seam")
    prevent_file(m, "this directory's specs must not touch <seam>")
```

Every spec in the directory imports `_prevention.spl` and calls
`arm_dir_prevention()` as the first line of its body. This is **opt-in per
file, not enforced by the runner** — a spec that forgets the import is
unprotected, and there is no mechanism today that would catch the omission.

The runner-support gap that would make this automatic and non-optional is
tracked in
`doc/08_tracking/bug/sspec_no_dir_wide_prevention_scope_2026-08-07.md`.

## See also

- `doc/03_plan/infra/testing/sspec_prevention_mock_plan_2026-08-07.md` — the
  full design (all five units).
- `doc/07_guide/infra/security/mock_policy_system_test_ban.md` — mock-creation
  ban policy (a different kind of prevention).
- `.claude/skills/spipe.md` § "Prevention mocks" — agent-facing summary.
- `doc/00_llm_process/feature_expert/prevention_mocks/skill.md` — LLM wiki
  entry for this feature.
