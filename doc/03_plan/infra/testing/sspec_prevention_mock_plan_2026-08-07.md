# SSpec Prevention Mocks — Deep Plan (2026-08-07)

**Goal:** Let a spec author declare *prevention mocks* — mocks whose purpose is to
FAIL the test when a forbidden call path is taken (real fs write in a pure test,
network in a unit test, DI mutation while locked, deprecated API) — at three
scopes: per-test (`it`), per-file (spec file), and directory-wide. Where the
architecture cannot express a scope, the gap is documented in the guide, the
spipe skill, and the LLM wiki instead.

**Audience:** each unit below is executable by a weaker model with no design
judgment. All design decisions are made here.

---

## Investigation findings (ground truth, verified 2026-08-07)

What exists TODAY:

- **Full mock library** (pure-Simple): `src/lib/nogc_sync_mut/src/testing/`
  - `mock/builder.spl` — `MockFunction` (call recording via `record_call`),
    `MockBuilder.returns(...)`, `MockRegistry`, `MockPolicy` +
    `mock_policy_init/disable/reset/allow_in_layer` (global policy object).
  - `mock/verification.spl` — `Matcher` (any/eq/gt/contains/predicate/...),
    `CallAnalyzer`, `verify_called(mockfn, times)` (line 128),
    `verify_called_with(mockfn, args)` (line 131), `Expectation.verify_all()`.
  - `mock/spy.spl` — `Spy` (method_called, method_call_count, total_calls).
  - `mocking_core.spl` is a facade re-exporting all three.
- **Mock-ban policy already exists** — `doc/07_guide/infra/security/mock_policy_system_test_ban.md`:
  `MockMode.All/HalOnly/Disabled/Custom`; `Mock.new()` panics when banned.
  That is prevention *of mocks*; this plan adds prevention *by mocks*.
- **Spec DSL**: `src/lib/nogc_sync_mut/spec.spl` — `describe/context/it`,
  `before_each/after_each` (global `before_hooks`/`after_hooks` arrays, lines
  33-35, 515-518), `_execute_it` (line 94) runs before hooks → block → after
  hooks → tallies via `current_test_errors`.
- **The prevention idiom exists but is manual**: `verify_called(m, 0)` at the
  end of an `it` body. Nothing auto-verifies; forgetting the check = fail-open.
- **No call interception.** Mocks only observe calls routed through them by
  composition/DI. A prevention mock CANNOT observe a direct
  `rt_file_write_text` or a real socket call — that requires seam injection
  (pass the mock where the dependency is consumed) or env-level probes
  (`src/lib/nogc_sync_mut/engine_probe.spl` for engine identity).
- **No per-directory config.** The runner reads one repo-level
  `config/simple.test.sdn` (`src/lib/nogc_sync_mut/test_runner/test_config.spl`
  line 34, `find_config_file` walks up from cwd only, lines 300-302). Spec
  discovery (`src/app/test_runner_new/`) has no per-dir fixture/helper hook.
  **Directory-wide scope is therefore NOT specifiable today** → Unit U4.

Scope verdicts:

| Scope | Specifiable? | Mechanism |
|-------|-------------|-----------|
| per-test (`it`) | YES | `prevent(...)` registered in `it`, auto-checked at end of `_execute_it` (U1+U2) |
| per-file | YES | `prevent_file(...)` at spec top level; checked after every `it` and cleared at process end (U2) |
| directory-wide | NO (needs runner discovery changes) | Convention + docs only: shared `_prevention.spl` helper each spec imports (U4) |

---

## Unit U1 — prevention core: `ForbiddenCallGuard`

**Files:** CREATE `src/lib/nogc_sync_mut/src/testing/mock/prevention.spl`;
EDIT `src/lib/nogc_sync_mut/src/testing/mock/__init__.spl` and
`src/lib/nogc_sync_mut/src/testing/__init__.spl` (add exports, mirroring how
`builder`/`verification`/`spy` are exported).

**Implementation (exact shapes; follow builder.spl style — no inheritance,
`static fn new`, copy-modify-assign for nested mutation):**

```simple
# src/lib/nogc_sync_mut/src/testing/mock/prevention.spl
# Prevention mocks: guards that FAIL verification when a forbidden
# call path was taken. See doc/07_guide/infra/testing/prevention_mocks.md
import testing.mock.builder: MockFunction, VerificationResult

class ForbiddenCallGuard:
    mockfn: MockFunction
    reason: text          # user-voice: WHY this call is forbidden
    max_allowed: i32      # normally 0; N>0 = "at most N" budget guards

    static fn new(mockfn: MockFunction, reason: text) -> ForbiddenCallGuard:
        ForbiddenCallGuard(mockfn: mockfn, reason: reason, max_allowed: 0)

    static fn at_most(mockfn: MockFunction, n: i32, reason: text) -> ForbiddenCallGuard:
        ForbiddenCallGuard(mockfn: mockfn, reason: reason, max_allowed: n)

    fn check() -> VerificationResult:
        val n = self.mockfn.calls.len()
        if n <= self.max_allowed:
            return VerificationResult.success()
        val name = self.mockfn.name
        VerificationResult.failure(
            "forbidden call: {name} called {n}x (allowed {self.max_allowed}) — {self.reason}")

pub fn check_guards(guards: [ForbiddenCallGuard]) -> [text]:
    var failures: [text] = []
    for g in guards:
        val r = g.check()
        if not r.ok:            # match VerificationResult field name in builder.spl
            failures.push(r.message)
    failures
```

Before writing, open `mock/builder.spl` lines 170-185 and use the ACTUAL
`VerificationResult` field names (`ok`/`message` may differ — copy what
`success()`/`failure()` set). Do not invent fields.

**Verify:** `bin/simple test test/01_unit/lib/std/testing/prevention_mock_spec.spl`
(spec written in U3; for U1 alone, `bin/simple lint` the new file and run U3's
spec after U2/U3 land).

**Done when:** file exists, lint-clean, exports resolve
(`grep -n prevention src/lib/nogc_sync_mut/src/testing/__init__.spl`).

**Collision set:** `src/lib/nogc_sync_mut/src/testing/**` (shared with nothing
else in this plan).

---

## Unit U2 — spec DSL integration: `prevent` / `prevent_file`

**Files:** EDIT `src/lib/nogc_sync_mut/spec.spl` ONLY. (The other three
`src/lib/*/spec.spl` re-export; check with `head -20` each — if any is a full
copy rather than a re-export, apply the same diff there. Known: gc_async_mut,
gc_sync_mut, nogc_async_mut.)

**Exact changes:**

1. Near the hook storage (after line 35 `var after_hooks = []`) add:

```simple
# Prevention-mock guards. test-scope cleared after every it;
# file-scope persists for the whole spec file.
var prevention_guards_test = []
var prevention_guards_file = []
```

2. New public API next to `before_each`/`after_each` (line ~515):

```simple
pub fn prevent(mockfn, reason: text):
    """Prevention mock: fail THIS example if mockfn is ever called."""
    prevention_guards_test.push(ForbiddenCallGuard.new(mockfn, reason))

pub fn prevent_at_most(mockfn, n: i64, reason: text):
    prevention_guards_test.push(ForbiddenCallGuard.at_most(mockfn, n, reason))

pub fn prevent_file(mockfn, reason: text):
    """Prevention mock checked after EVERY example in this spec file."""
    prevention_guards_file.push(ForbiddenCallGuard.new(mockfn, reason))
```

Import at top of spec.spl: `use std.src.testing.mock.prevention.{ForbiddenCallGuard, check_guards}`
— match the import path style already used elsewhere for `testing` modules
(`grep -rn "use.*testing.mock" src/lib/nogc_sync_mut/ | head` first; use the
form that resolves, e.g. via the `testing/__init__.spl` export added in U1).

3. In `_execute_it` (line 94), after the after_each loop (line 114) and BEFORE
the result check (line 116), add:

```simple
    # Prevention-mock auto-verification (test-scope + file-scope)
    for msg in check_guards(prevention_guards_test):
        current_test_errors.push(msg)
    for msg in check_guards(prevention_guards_file):
        current_test_errors.push(msg)
    prevention_guards_test.clear()
```

Notes for the implementer: use `.clear()` not rebinding (comment at line 100
explains why rebinding globals breaks under writeback); file-scope guards are
NOT cleared (whole-file lifetime); file-scope MockFunctions accumulate calls
across examples — document in U4's guide that `prevent_file` mocks should be
freshly reset in `before_each` when per-example isolation is wanted, via
`before_each(\: my_mock.calls.clear())` — verify `MockFunction.calls` is
directly clearable; if not, recreate the mock in `before_each`.

**Verify:** U3 spec passes; then sabotage per U3 step 4.

**Done when:** `prevent`/`prevent_at_most`/`prevent_file` callable from a spec,
a triggered guard turns the example FAILED with the reason text in the error
line, and an untriggered guard leaves counts unchanged.

**Collision set:** `src/lib/*/spec.spl` — HIGH-TRAFFIC shared file; single
agent only, commit immediately (anti-clobber protocol).

---

## Unit U3 — spec + sabotage recipe

**File:** CREATE `test/01_unit/lib/std/testing/prevention_mock_spec.spl`
(sibling of existing `mock_spec.spl`). Modern-SSpec style: user-voice `"""..."""`
docstring, `step("...")`, outcome-named its, `# @req REQ-PREVENT-MOCK-1`.

**Named `it` blocks (write exactly these):**

```
describe "prevention mocks":
  it "a prevention mock that is never called leaves the example green"
  it "a forbidden call fails the example and names the mock and the reason"
  it "prevent_at_most allows the budget and fails on budget+1"
  it "verify_called with zero times is the manual equivalent"     # bridges old idiom
describe "prevention mock file scope":
  it "prevent_file guard is checked on every example"             # guard armed at file top
  it "file guard failure message carries the file-scope reason"
```

Sketch of the core positive/negative pair (adapt to actual API from U1):

```simple
use std.spec.*
use std.testing.{MockFunction}   # use the resolving import path from U1

it "a forbidden call fails the example and names the mock and the reason":
    step("declare a prevention mock for the deprecated writer")
    val m = MockFunction.new("legacy_write")
    prevent(m, "legacy_write is deprecated; use write_v2")
    step("code under test takes the forbidden path")
    m.record_call(["/tmp/x"])
    # _execute_it will now record a failure — this example is asserted
    # via the sabotage recipe below, not inline (a failing example cannot
    # assert its own failure). Keep it in the file but under slow_it OR
    # move it to the sabotage recipe only. DECISION: implement it as a
    # self-checking variant instead:
    val msgs = check_guards([ForbiddenCallGuard.new(m, "deprecated")])
    expect(msgs.len()).to_equal(1)
    expect(msgs[0]).to_contain("legacy_write")
    prevention_guards_test.clear()   # do not fail the example itself
```

(If `prevention_guards_test` is not reachable from the spec, drop the `prevent`
call in this negative example and test only `check_guards` directly — the
end-to-end failing path is covered by the sabotage recipe.)

**Sabotage recipe (spell-out; proves the wiring is not fail-open):**

1. `cp test/01_unit/lib/std/testing/prevention_mock_spec.spl /tmp/claude-1000/prevention_sabotage_spec.spl` — no: runner needs it under test/; instead create `test/01_unit/lib/std/testing/prevention_mock_sabotage_spec.spl` TEMPORARILY with one it: arm `prevent(m, "sabotage")`, then `m.record_call([])`, then assert nothing.
2. `bin/simple test test/01_unit/lib/std/testing/prevention_mock_sabotage_spec.spl > /tmp/claude-1000/prev_sab.log 2>&1; echo exit=$?` — capture to file, take `$?` from the command (testing.md rule).
3. `tail -5 /tmp/claude-1000/prev_sab.log` MUST show `FAILED`, the string `forbidden call: `, and a non-zero exit. If it shows ok/exit 0, U2's hook is fail-open — STOP and fix before proceeding.
4. DELETE the sabotage file (`rm`) — it must never land.

**Verify:** `bin/simple test test/01_unit/lib/std/testing/prevention_mock_spec.spl`
→ read the final `Results:` line only (authoritative), all green.

**Done when:** spec green, sabotage red-then-deleted, `# @req` comments present.

**Collision set:** `test/01_unit/lib/std/testing/` only.

---

## Unit U4 — directory-wide scope: docs + skill + wiki (the unspecifiable scope)

Dir-wide prevention is NOT implementable without test-runner discovery changes
(no per-dir config, no shared-fixture hook). This unit ships the convention +
documentation instead, and files the runner feature.

**Files:**

1. CREATE `doc/07_guide/infra/testing/prevention_mocks.md` with sections:
   - *What a prevention mock is* (fail-on-forbidden-call vs stub) and the two
     supported scopes with one example each (`prevent` in an it;
     `prevent_file` at file top).
   - *What it cannot see*: no interception — real `rt_*`/fs/network calls are
     invisible unless the dependency is injected; point to seam injection and
     `engine_probe.spl` for engine-identity prevention; cross-link
     `doc/07_guide/infra/security/mock_policy_system_test_ban.md`.
   - *Directory-wide convention (until runner support lands)*: put a
     `_prevention.spl` helper in the spec directory exporting
     `fn arm_dir_prevention():` that calls `prevent_file(...)` for the dir's
     forbidden seams; every spec in the dir imports and calls it first line of
     the file body. State plainly: this is opt-in per file, NOT enforced by the
     runner; a spec that forgets the import is unprotected.
   - *Runner feature request*: link the bug/feature record (next bullet).
2. CREATE `doc/08_tracking/bug/` record
   `sspec_no_dir_wide_prevention_scope_2026-08-07.md`: gap = discovery in
   `src/app/test_runner_new/` + `test_config.spl` `find_config_file`
   (repo-level only, lines 300-302); unblock condition = per-directory
   config/fixture hook in spec discovery.
3. EDIT `.claude/skills/spipe.md`: extend the "Prevention mocks" section
   (added 2026-08-07, after "Fixtures that lie") with the `prevent`/
   `prevent_file` DSL once U2 lands, and the dir-convention pointer.
4. CREATE LLM wiki `doc/00_llm_process/feature_expert/prevention_mocks/skill.md`
   from `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`: Role =
   own prevention-mock process knowledge; Feature Links → this plan, the guide
   (1), the tracking record (2), source `src/lib/nogc_sync_mut/src/testing/mock/prevention.spl`
   and `src/lib/nogc_sync_mut/spec.spl`; Update Rule/Checklist copied from
   template. Also EDIT the relevant layer expert if
   `doc/00_llm_process/layer_expert/` has a testing/spec layer entry
   (`ls doc/00_llm_process/layer_expert/`) — add a link line; if none exists,
   skip (do not create a new layer).

**Done when:** all four artifacts exist, guide ≤1 screen of code per example,
`doc/07_guide/infra/testing/` stays ≤10 files.

**Collision set:** `.claude/skills/spipe.md` (shared with this plan's landing
commit — rebase-merge, do not overwrite the 2026-08-07 section).

---

## Unit U5 — adoption: 3 concrete specs (all verified to exist)

1. `test/01_unit/compiler/di/di_lock_spec.spl` — already stubs `DiContainer`
   with a `locked` flag. Add a `MockFunction.new("di_bind_while_locked")`,
   `record_call` inside the stub's `bind_instance` when `self.locked`, and
   `prevent(m, "DI mutation while locked must be rejected, not recorded")` in
   the lock-enforcement examples — turning silent accept into a failure.
2. `test/01_unit/app/devhub/adapter_bitbucket_spec.spl` — unit spec over a
   network adapter. Route the transport seam through a
   `MockFunction.new("real_http_send")` and `prevent_file(m, "unit specs must
   not hit the network")` at file top; existing stubs keep answering.
3. `test/01_unit/lib/common/mock_verification_spec.spl` — dogfood: add one
   example `it "verify_called(m, 0) doubles as a manual prevention check"`
   asserting both directions (0 calls → true; 1 call → false).

Each is its own commit; run the file before AND after
(`bin/simple test <path>` twice, compare the `Results:` lines — counts must
not shrink).

**Collision set:** the three spec files only.

---

## Execution order & sizing

U1 → U2 → U3 (strictly serial; one agent each). U4 parallel to U3 (doc-only,
but its spipe.md edit lands after U2 so the DSL section is truthful).
U5 after U3 green. Every unit: lint changed `.spl` files, commit + push
immediately per fix (plumbing landing, fixed index path, 3 pre-push guards,
ls-remote verify).
