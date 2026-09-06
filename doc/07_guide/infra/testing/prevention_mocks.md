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

**The manual idiom still works** and remains useful when you want to inline
the check without an import: assert `verify_called(m, 0)` at the end of the
`it` body:

```simple
val m = MockFunction.new("legacy_write")
# ... exercise the code under test, injecting `m` at the seam ...
val result = verify_called(m, 0)
assert_true(result.passed)
```

Nothing auto-verifies this form. If the assertion is forgotten, the example
stays green even if the forbidden call happened — this idiom is fail-open by
construction. Prefer the DSL below, which fails loudly by design.

## Landed: `prevent` / `prevent_at_most` / `prevent_file` DSL (2026-08-07)

`src/lib/nogc_sync_mut/src/testing/mock/prevention.spl` adds
`ForbiddenCallGuard` (`.new(mockfn, reason)`, `.at_most(mockfn, n, reason)`)
and `check_guards(guards)`. `src/lib/nogc_sync_mut/spec.spl` wraps those as a
first-class spec DSL — one line instead of the three-line manual idiom above:

```simple
use std.nogc_sync_mut.src.testing.mock.builder.{MockFunction}
use std.nogc_sync_mut.spec.{prevent, prevent_at_most, prevent_file}

it "never hits the network":
    val m = MockFunction.new("real_http_send")
    # ... exercise the code under test, injecting `m` at the seam ...
    prevent(m, "unit specs must not hit the network")
```

**Import explicitly, fully-qualified.** `use std.spec.*` (the wildcard form
most of the suite relies on) does not reliably expose every `pub fn` in
`spec.spl`, including long-standing ones — a pre-existing wildcard-import
gap unrelated to this DSL. Always import
`use std.nogc_sync_mut.spec.{prevent, prevent_at_most, prevent_file}`
explicitly. Details: Defect 3 in
`doc/08_tracking/bug/prevention_mock_deferred_arming_impossible_2026-08-07.md`.

**Ordering contract — call `prevent`/`prevent_at_most`/`prevent_file` AFTER
the code under test has run, never at the top of the `it` body.** The
original design here called for "arm early, auto-check at the end of
`_execute_it`" (the two bullets a previous revision of this guide described
as the planned per-test/per-file scopes). That design is impossible under
this interpreter: a `MockFunction` stored in an array, class field, or
closure is copied by value, so a guard armed before the forbidden call
always reports zero calls — a fail-open DSL. Full repro:
`doc/08_tracking/bug/prevention_mock_deferred_arming_impossible_2026-08-07.md`.

All three functions instead check **immediately** against the mock's current
state at the call site — the same mechanism as a failed `expect`:

- **`prevent(mockfn, reason)`** — fails the example right now if `mockfn` has
  been called (`max_allowed: 0`).
- **`prevent_at_most(mockfn, n, reason)`** — budget variant; fails if called
  more than `n` times.
- **`prevent_file(mockfn, reason)`** — a documented alias for `prevent`, NOT
  true auto-checked file scope (module-level spec state does not persist
  across `it` examples under this runner — same root cause as the
  directory-wide gap below). Call it explicitly in every example (or from
  `before_each`/`after_each` with a mock rebuilt each time) to approximate
  file-wide coverage.

Adoption examples: `test/01_unit/compiler/di/di_lock_spec.spl` (guarded
DI-mutation-while-locked seam), `test/01_unit/lib/common/mock_verification_spec.spl`
(dogfoods the manual idiom), `test/01_unit/app/devhub/adapter_bitbucket_spec.spl`
(documents a seam with no fetcher-injection point — the guard records the
invariant rather than intercepting a real call; see "What prevention mocks
cannot see" below).

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
use std.nogc_sync_mut.spec.{prevent_file}
use std.nogc_sync_mut.src.testing.mock.builder.{MockFunction}

pub fn arm_dir_prevention():
    """Call this as the first line of every spec body in this directory,
    AFTER the code under test has run (see the ordering contract above)."""
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

## Don't land a guard you can't drive red

A `prevent`/`prevent_at_most`/`prevent_file` call that is wired to a mock no
code path can ever reach is decorative, not evidence — it will always report
zero calls whether or not the invariant it names actually holds. Before
landing an adoption, sabotage it: temporarily force the guarded seam to be
called (or lower an `at_most` budget below the real call count) and confirm
the example goes RED with a `forbidden call: ...` message naming the mock and
reason, then restore. If a spec has no injectable seam for the call you want
to prevent (see "What prevention mocks cannot see" above), either find a real
seam (a function parameter the code under test actually threads through,
not a closure capture reached only via another function's call stack — closures
captured across a call boundary hit the same by-value-copy defect as deferred
arming) or document the guard's non-interceptive, invariant-recording purpose
explicitly at the call site, as `adapter_bitbucket_spec.spl` does — do not
claim it intercepts a call it structurally cannot see.

## See also

- `doc/03_plan/infra/testing/sspec_prevention_mock_plan_2026-08-07.md` — the
  full design (all five units).
- `doc/08_tracking/bug/prevention_mock_deferred_arming_impossible_2026-08-07.md`
  — why the DSL checks immediately instead of arming early.
- `doc/08_tracking/bug/sspec_no_dir_wide_prevention_scope_2026-08-07.md` —
  directory-wide scope gap.
- `doc/07_guide/infra/security/mock_policy_system_test_ban.md` — mock-creation
  ban policy (a different kind of prevention).
- `.claude/skills/spipe.md` § "Prevention mocks" — agent-facing summary.
- `doc/00_llm_process/feature_expert/prevention_mocks/skill.md` — LLM wiki
  entry for this feature.
