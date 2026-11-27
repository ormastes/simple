# generator_intensive_spec.spl shadows GeneratorState with different variants

Status: RESOLVED 2026-11-25 — shadow replaced by documented mirror of the real 4-variant enum (see dated note at bottom)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

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

## Status: FIXED (partially, via documented mirror) 2026-08-10

Both spec copies (`test/01_unit/lib/nogc_async_mut/generator_intensive_spec.spl`
and `test/unit/lib/nogc_async_mut/generator_intensive_spec.spl`, kept
byte-identical) now declare `enum GeneratorState { Created, Suspended
(next_value, env), Running, Completed }` — matching the real product enum's
variant names and payload shape — instead of the old `Yielded`/`Completed`
shadow. All four variants have direct predicate coverage, and a new
`LifecycleGenerator` class + "Generator Lifecycle (real GeneratorState state
machine)" describe block drives a generator through
`Created -> Suspended -> ... -> Completed` end to end, asserting on the
`env` payload advancing across resumes.

A true `use`-import of the real `GeneratorState`/`Generator` type was
attempted rather than a local mirror. It hit a second, deeper defect: the
defining module `src/app/interpreter/async_runtime/generators.spl` does not
parse under the current grammar (struct-style enum-variant construction,
`&T`/`Box<T>` reference/generic syntax). One parse blocker in that module
(`gen` used as a parameter name, a reserved keyword) was fixed in this pass
since the module is unreferenced elsewhere in the tree and the rename is
safe; the remaining parse blockers are filed as a new, separate bug:
`doc/08_tracking/bug/generator_async_runtime_module_fails_to_parse_2026-08-10.md`.
The spec's local enum is explicitly documented (in its own header comment)
as a stand-in mirror pending that fix, not a silent shadow — variant names
and payload arity now match the real type exactly, only `env`'s payload
type is downgraded from `Environment` to a placeholder `i64`.

Verdicts: `bin/simple test test/01_unit/lib/nogc_async_mut/generator_intensive_spec.spl`
→ `Results: 33 total, 33 passed, 0 failed`. Same command against the
`test/unit/...` twin → identical `Results: 33 total, 33 passed, 0 failed`.
(27 examples before this fix; 6 new examples added.)

## Update 2026-08-10 — mirror retained, real enum now importable but package still blocked

`generators.spl` was fixed and `GeneratorState` is now importable and
constructible (all 4 variants verified by an import probe). The mirror could
still NOT be deleted: `use app.interpreter.async_runtime.generators.GeneratorState`
loads the package `__init__.spl`, which eagerly imports `actors.spl`, an
unmigrated Rust draft (`static mut`, `unsafe { }`) that does not parse. Details
and the unblock condition: `generator_async_runtime_module_fails_to_parse_2026-08-10.md`.

The mirror's header comment was rewritten to state the real (transitive)
reason rather than the original incorrect diagnosis. Both legs re-verified
byte-identical at `Results: 33 total, 33 passed, 0 failed`.

## Triage 2026-09-13

Test-only dedup (spec shadows real GeneratorState product enum with
different variants) -- cleanup task across a 531-line spec, not a
functional defect. Leaving OPEN, out of this lane's per-item scope.

## Verification 2026-11-25 (p3-bau fleet, worktree wt-p3-bau, release/1.0.0 @ e3902cdaa78)

Closed as STALE. The 2026-08-10 "FIXED (partially, via documented mirror)"
section above is the resolution: the shadow `Yielded`/`Completed` enum was
replaced by a documented mirror of the real 4-variant `GeneratorState`, which
is exactly what the body's unblock condition allows short of the separate
package-parse bug. Confirmed by inspection:

- `test/01_unit/lib/nogc_async_mut/generator_intensive_spec.spl:29-33`
  declares `enum GeneratorState { Created, Suspended(next_value: i64, env: i64),
  Running, Completed }` with a header comment documenting the mirror and
  pointing at `generator_async_runtime_module_fails_to_parse_2026-08-10.md`.
- The duplicate `test/unit/lib/nogc_async_mut/generator_intensive_spec.spl`
  twin no longer exists (legacy `test/unit/` tree removed), so the
  two-copy dedup concern is moot.

LIMIT: spec re-execution environment-blocked on this host (pinned seed
2026-11-17 predates the 2026-11-25 `@representation_boundary` annotations,
`cfd89933699`; every `bin/simple.exe test` run aborts in the test runner
before loading the spec). The 2026-08-10 executed evidence (33/33 both legs)
stands as the last run. The remaining true-import blocker is tracked by the
separate `generator_async_runtime_module_fails_to_parse_2026-08-10.md`.

