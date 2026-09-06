# `match` on an `Option<enum>` value falls through to the wildcard arm

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## RE-ATTRIBUTION (2026-08-17) — this is an INTERPRETER defect, not a MIR one

This row was triaged into the `src/compiler/50.mir/**` lane against
`_MirLoweringExpr/switch_operators_calls.spl`. That attribution is **wrong** and
sent the row to the wrong owner. Measured today by running the same program
under both engines (`bin/simple` is the Rust seed, mtime 2026-08-16 22:59):

```
$ SIMPLE_EXECUTION_MODE=jit         bin/simple run probe.spl   ->  ARM-ACTION     (correct)
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run probe.spl   ->  ARM-WILDCARD   (wrong)
```

on `enum Ev: Action(name: text) / Other`, `fn mk() -> Ev?` returning
`Ev.Action(name: "go")`, matched with an `Ev.Action(n)` arm and a `_` arm.

So the JIT — the engine 50.mir lowering feeds — selects the variant arm
correctly, and the **tree-walk interpreter** is the arm that falls to the
wildcard. The defect lives in the interpreter's match/pattern path, not in MIR
lowering. Fixing 50.mir would change nothing here.

Reproducing spec (RED today):
`test/01_unit/compiler/codegen/cross_engine_silent_divergence_spec.spl`
with run-path probe `probe_cross_engine_silent_divergence.spl`.
Note the spec asserts the INTERPRETER selects the variant arm, and pins the JIT
as a control arm so a fix cannot regress it.

---

**Found:** 2026-08-07, while implementing Simple Lab UI (Stream L, task L2 of
`doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md`).
**Binary:** `bin/simple` (currently the Rust-built bootstrap seed at
`bin/release/x86_64-unknown-linux-gnu/simple` — deployed self-hosted binary
prints the seed warning banner; not re-verified against a genuine
self-hosted build).

## Symptom
`common.ui.semantic_contract.semantic_ui_command_to_event(command) -> UIEvent?`
returns a non-nil `UIEvent` for every `SemanticUiCommand` command type it
recognizes (click/type/key/action/focus/...). Matching that `UIEvent?`
result directly against enum variant patterns silently takes the wildcard
`_` arm instead of the matching variant arm:

```simple
match semantic_ui_command_to_event(command):
    UIEvent.Action(name):
        ...        # never reached
    _:
        ...        # always reached, even when the value is Some(UIEvent.Action(...))
```

Confirmed with a minimal repro (`app.simple_lab.main.SimpleLabApp` +
`SemanticUiCommand.action("main", "lab_add_cell")`): `if event != nil:` takes
the true branch and successfully dispatches; the equivalent `match` always
falls to `_`.

This is not new to Simple Lab — the pre-existing
`test/01_unit/app/ui/semantic_contract_spec.spl` example "maps semantic
commands to existing UI events" (which does exactly this match-on-Option
pattern) already fails on this binary (`bin/simple test
test/01_unit/app/ui/semantic_contract_spec.spl` → 4 of 12 examples fail,
including that one and two others — `dispatches semantic commands through
UISession state and access history`, `routes semantic commands to their
named surface` — that also destructure/consume `semantic_ui_command_to_event`
results downstream of a `UISession` path).

## Workaround
Use a nil-check instead of matching the optional value directly:

```simple
val event = semantic_ui_command_to_event(command)
if event != nil:
    app.handle_event(event)
```

This is what `src/app/simple_lab/main.spl` consumers
(`test/01_unit/app/simple_lab/lab_ui_semantic_spec.spl`) do to avoid the
defect.

## Unblock condition
Re-run `bin/simple test test/01_unit/app/ui/semantic_contract_spec.spl` after
a genuine (non-seed) self-hosted `bin/simple` rebuild; if the 4 failures
persist, the defect is in the interpreter/JIT's match-on-`Option<enum>`
lowering (likely `Option` flattening not applying when matched against bare
enum-variant patterns) and needs a fix in the compiler's match desugaring,
not in caller code.
