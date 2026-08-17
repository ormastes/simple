# `IntoAction` and `CommonAction` are imported and implemented but declared nowhere

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Found:** 2026-08-04, by `scripts/check/check-trait-arity.spl` while closing
  the not-found bucket of
  `doc/08_tracking/bug/trait_conformance_check_ignores_arity_2026-08-04.md`
- **Severity:** a passing spec asserts against a trait that does not exist.

## What

`test/01_unit/app/ui/typed_action_spec.spl` — and its byte-identical duplicate
`test/unit/app/ui/typed_action_spec.spl` — opens with

```
use common.ui.action.{Action, CommonAction, IntoAction}
```

and at line 20 declares

```
impl IntoAction for AppAction:
    fn into_action(self) -> Action:
        ...
```

But `src/lib/common/ui/action.spl` declares exactly one item, `class Action:`.
Neither `IntoAction` nor `CommonAction` is declared anywhere in the tree: the
only two files in the repo that mention either name are the two copies of this
spec.

## Why it is silent

An unresolved `use` is only a warning, not an error — the process still exits 0
(`reference_unresolved_use_is_only_a_warning...`). So the spec compiles, runs,
and reports green while `impl IntoAction for AppAction` conforms to nothing:
there is no declaration for the conformance check to compare against, in either
the name-only form it has today or the arity form proposed in the parent bug.
The spec's own describe blocks — `"app-defined IntoAction"` (line 107) and
`"CommonAction impl IntoAction"` (line 122) — are named after behaviour that has
no implementation behind it.

## Scope of the claim

The arity checker classifies this as *trait not found*, which is the honest
verdict: an undeclared trait cannot be scored for drift. It is reported here
rather than in the parent bug because it is a UI-lane feature gap, not
trait-arity work, and arming the arity check would not surface it.

## What an owner needs to decide

Either `IntoAction`/`CommonAction` were planned and never landed — in which case
the spec is asserting a feature that does not exist and should be marked pending
rather than left green — or they were removed and the spec was not. Reproduce
with:

```
bin/simple run scripts/check/check-trait-arity.spl --list-unscorable
```

which prints the two `NOT-FOUND IntoAction.into_action on AppAction` records.

Do not "fix" this by deleting the spec: which of the two histories applies
determines whether a real UI feature is missing.

---

## Resolution (2026-08-04) — FIXED: never written, now implemented

**Status: CLOSED.**

### 1. Which history applied: never written

`git log -S 'IntoAction' -- src/lib/common/ui/` and
`git log -S 'CommonAction' -- src/lib/common/ui/` both return **zero commits**.
`git log --follow -- src/lib/common/ui/action.spl` reaches back to
`97a9358145f`, and `git show 97a9358145f:src/lib/common/ui/action.spl` is
byte-identical to the version at `ab4cbc17b8f`. The file was a 194-byte
`class Action { name: text }` stub from the day it was created and never
changed. Neither symbol was deleted or renamed — **they were never written.**

### 2. Owner intent was documented and explicit

`doc/01_research/ui/protocol/ui_modernization_plan.md` §"Phase 5 — Typed
actions/events" specifies verbatim:

```
enum CommonAction { Save, Cancel, Confirm, Dismiss, Back, Search, ToggleSidebar }
enum Action { Builtin(CommonAction), Custom(text) }
trait IntoAction { fn into_action(self) -> Action }
```

in "new `src/lib/common/ui/action.spl`", with exit gate "a new
`typed_action_spec.spl`". `doc/05_design/language/misc/ui001_unblock_plan.md`
line 173 *claims* `action.spl` already ships
"`Action`/`CommonAction`/`IntoAction`" — a false completion claim; only the
spec and the stub were landed.

### 3. The spec was NOT green — the premise above is corrected

The bug as filed says "a passing spec asserts against a trait that does not
exist". Measured on a pristine worktree at `ab4cbc17b8f`:

```
Results: 19 total, 0 passed, 19 failed
```

All 19 examples failed. The spec was **honestly red**, not vacuously green —
it is a correct spec for an unimplemented feature, not a member of the
false-green family. The unresolved-`use`-is-a-warning behaviour let the file
*load*, but every assertion still failed. What the warning hid was the
*reason* (missing declarations), not the failure itself.

### 4. Fix

`src/lib/common/ui/action.spl` now declares the RFC API exactly as specified:
`enum CommonAction` (7 variants) with `to_wire()`, `enum Action` with
`Builtin(action: CommonAction)` / `Custom(name: text)` and `into_wire_name()`,
`trait IntoAction { fn into_action(self) -> Action }`, and
`impl IntoAction for CommonAction`.

The wire shape is unchanged: `UIEvent.Action(name: text)` still carries one
text field. The two existing consumers — `ui_event_action` (event.spl:551) and
`with_on_typed_action` (builder.spl:507) — only call `.into_wire_name()`, so
the `class` -> `enum` change is source-compatible. `Action.named(...)` had zero
call sites and was dropped per the RFC shape.

### 5. Non-vacuity proof (sabotage)

Implemented, unmodified:

```
Results: 19 total, 19 passed, 0 failed
```

Sabotage — two lines in `action.spl`: `CommonAction.Save => "save"` changed to
`"sabotaged"`, and the `Action.Custom(name)` arm's `return name` changed to
`return "SABOTAGED"`:

```
Results: 19 total, 10 passed, 9 failed
```

The 9 reds include `AppAction.OpenFile routes to open_file via into_action` and
`CommonAction.Save into_action returns Action.Builtin with save wire name`,
which proves the trait dispatch and the payload extraction are really executing
— not short-circuiting. Restored to the unmodified file, back to
`19 total, 19 passed, 0 failed`.

### 6. Sibling sweep — this is a family

Method: extract every name from braced `use path.{A, B}` imports in
`test/**/*_spec.spl` (11,645 distinct); build a declaration index over owned
`src/` + `test/` `.spl` (vendored paths excluded) from line-start
`class|struct|enum|trait|type|impl|fn|val|var|const|alias|actor|mixin NAME`
plus `export A, B` re-export lists (195,855 distinct); subtract.

**380 distinct imported names are declared nowhere, across 282 spec files.**
Heaviest: `test/{01_,}unit/app/t32_cli/error_codes_spec.spl` (29 each),
`test/03_system/feature/app/t32_tools/t32_mcp_spec.spl` (21),
`test/{01_,02_}integration/hardware/rv32imac/rv32_core_smoke_spec.spl` (13).

Error modes of the method, stated: only braced `use x.{A,B}` is scanned, so
`use x.*` and bare `use x` are missed (**undercount**); the declaration index is
grep-based on line-start forms, so an unusually-indented declaration reads as
missing (**false positive**); names are matched repo-wide rather than by module
path, so a symbol declared in the *wrong* module still counts as declared
(**undercount**). Spot-check of 5 sampled names (`AluOp`,
`chacha20_keystream`, `CoverageConfig`, `AckProgram`, `AnsiState`) found zero
occurrences anywhere in `src/` — 0/5 false positives on that sample.

Only the `IntoAction`/`CommonAction` case was fixed here; the remaining 379 are
unverified individually and are left as a filed family, not a claim.

### 7. Regression check on the neighbouring wire oracle

`test/01_unit/app/ui/wire_golden/wire_golden_spec.spl` reads
`Results: 4 total, 2 passed, 2 failed` both with the original stub
`action.spl` and with the implementation — unchanged, so this change causes no
regression there. Its import closure (`std.spec.*` and `common.ui.access.{...}`)
never reaches `common.ui.action`, `builder`, or `event`. Separately worth
filing: `doc/05_design/language/misc/ui001_unblock_plan.md:177` claims this
spec is "wire byte oracle (4/4)"; it is 2/4, a second stale completion claim
in the same document.

### 8. Lint

`bin/simple lint` on the new `action.spl`: `Found 0 error(s), 2 warning(s)`.
Both warnings are `non_exhaustive_match` on the two `match self` blocks, which
are in fact exhaustive over their enums; the same pattern is used by
`src/lib/common/ui/widget_kind.spl`. Not suppressed — adding a `todo()`
catch-all would weaken the sabotage signal for no benefit.
