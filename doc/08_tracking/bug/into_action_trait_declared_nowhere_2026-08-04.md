# `IntoAction` and `CommonAction` are imported and implemented but declared nowhere

- **Status:** OPEN
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
