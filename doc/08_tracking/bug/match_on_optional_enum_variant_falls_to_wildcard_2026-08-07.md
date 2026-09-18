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

## Triage 2026-09-13

Reproduces on the deployed seed: `bin/simple test test/01_unit/compiler/codegen/cross_engine_silent_divergence_spec.spl --no-session-daemon` -> `7 total, 4 passed, 3 failed`, matching the recorded defect. Per the 2026-08-17 re-attribution, the defect lives in the tree-walk interpreter (not the pure-Simple `50.mir` lowering), and no pure-Simple interpreter implements `match` dispatch under `src/compiler/95.interp` — this is the Rust seed's interpreter (`src/compiler_rust/compiler/src/interpreter/**`). Fixing it needs a cargo build/redeploy cycle, out of scope for this pure-Simple TDD pass. Leaving OPEN, no code change made.

## Re-measurement 2026-09-18 — reproduces on BOTH lanes, and it belongs to a family

Binary: `bin/simple` as redeployed 2026-09-18 (`308de6af84db5c26e2c0`, built from
`origin/main`). Measurements on this host before 2026-09-18 17:00 used a binary
with its own silent wrong answers and are not comparable.

```simple
enum Evt:
    Click(x: i64)
    Key(code: i64)

fn make() -> Evt?:
    Some(Evt.Click(x: 5))

fn main() -> i64:
    match make():
        case Evt.Click(x): print "direct=click{x}"
        case Evt.Key(c):   print "direct=key{c}"
        case _:            print "direct=WILDCARD"
    0
```

| shape | interpret | JIT |
|---|---|---|
| `Evt?` matched against BARE variant patterns | **WILDCARD** | **WILDCARD** |
| same value matched as `case Some(Evt.Click(x))` | `click5` | `click5` |

So it still reproduces, both engines agree, and the `Some(...)`-wrapped form is
the one that works. Whether a bare variant pattern *should* match an optional
scrutinee is a design question and this entry does not settle it — but silently
selecting the wildcard is the worst of the three available answers, because it
produces a plausible wrong branch rather than either a match or a diagnostic.
With no wildcard arm present the same shape falls through silently instead
(`match_enum_fallthrough_silent_2026-08-01`).

### It is one family with two other open entries

All three are the same missing check — pattern/argument type agreement is not
enforced, so a mismatch resolves to a silent answer instead of a diagnostic:

| entry | shape | today |
|---|---|---|
| this one | non-Option pattern vs **Option** scrutinee | silently takes `_` |
| `option_pattern_accepted_on_non_option_scrutinee_2026-07-27` | Option pattern vs **non-Option** scrutinee | silently accepted, engines bind different values |
| `bool_typed_parameter_accepts_non_bool_and_jit_corrupts_it_2026-08-04` | `i64` argument vs **`bool`** parameter | silently accepted, `take_bool(5)` prints `got=true` |

They are mirror images of one another and should be priced as one job. Note
before attempting it: enforcement has blast radius, which is exactly why
`match_enum_fallthrough_silent_2026-08-01` chose a runtime diagnostic over a
compile-time checker after measuring 286 candidate sites and 336 enum names
declared more than once. Any fix here deserves the same measurement first.
`src/compiler/30.types/bidirectional_checking.spl` is where argument agreement
lives; PR #1077 is open on the sibling `type_infer/*` files.
