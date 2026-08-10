# generator_intensive_spec.spl shadows GeneratorState with different variants

- **File**: `test/unit/lib/nogc_async_mut/generator_intensive_spec.spl:17` (531 lines)
- **Real product code**: `src/app/interpreter/async_runtime/generators.spl:10`
  — `enum GeneratorState` with variants `Created`, `Running`,
  `Suspended(next_value, env)`, `Completed`, driving a real `Generator` class
  whose `next()`/`send()` logic threads an interpreter `env` through
  suspension/resumption.
- **Found during**: continuation of the SHADOW-family spec vacuity sweep
  (worklist row 108).

## What's wrong

The spec declares its own `enum GeneratorState` with variants `Yielded(value)`
and `Completed` only — no `Created`/`Running`/`Suspended` states, and no
`env`-threading concept at all. Its own `Generator`-like class advances a
`current` counter locally rather than driving the real interpreter's
generator suspend/resume machinery. Because the real product enum has two
variants (`Created`, `Running`, `Suspended`) with no counterpart in the local
enum, and the real `Suspended` variant carries an `env` payload the local
model has no equivalent for, an import-swap is not a rename — every state
transition assertion in the file would need to be re-derived against the real
suspend/resume state machine.

## Why not fixed in this pass

Same class of finding as `narrowing_spec`/`riscv_dual_arch_spec`: the real
type's variant set and payload shape differ enough that this needs a genuine
rewrite of the state-transition assertions against real `Created` →
`Running` → `Suspended`/`Completed` semantics, not a bounded import swap.

## Unblock condition

Rewrite the spec against the real `GeneratorState` enum and `Generator`
class in `src/app/interpreter/async_runtime/generators.spl`, exercising all
four real variants (including `Suspended`'s `env` payload across a real
yield/resume), not just a two-state `Yielded`/`Completed` model.
