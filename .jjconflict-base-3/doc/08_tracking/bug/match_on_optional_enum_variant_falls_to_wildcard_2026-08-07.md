# `match` on an `Option<enum>` value falls through to the wildcard arm

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
