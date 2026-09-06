# Interpreter: `use <module> as time` alias unresolvable — "variable `time` not found"

Date: 2026-07-02
Status: fixed (verified 2026-08-06; root cause already resolved upstream, no code change required)
Severity: P2
Related: game2d headless run path

## Symptom

Aliasing a module import to the name `time` makes every call through the alias
fail at runtime under `bin/simple run` (interpreter path):

```simple
use std.nogc_sync_mut.game2d.time.det_guard as time
...
time.set_deterministic_mode(true)   # error: semantic: variable `time` not found
```

Renaming the alias (e.g. `as det_time`) with no other change resolves it, so
the alias mechanism itself works — the name `time` is special-cased or
shadowed (likely by the builtin `time` module) during interpreter resolution.

## Repro (verified 2026-07-02)

Before the rename, any game2d example hit it at startup:

```bash
env SIMPLE_GAME_HEADLESS=1 bin/simple run examples/11_advanced/game2d/breakout/main.spl
# error: semantic: variable `time` not found
```

## Workaround

`src/lib/nogc_sync_mut/game2d/app/run.spl` and
`src/lib/nogc_sync_mut/game2d/loop/driver.spl` now alias as `det_time`.

## Expected

A local `use ... as X` alias should win over (or at least be resolvable
alongside) any builtin module named `X`, or the collision should be a
compile-time error — not a runtime "variable not found".

## Root cause (found 2026-08-06)

The colliding name was never a true stdlib "builtin" module — the seed has no
bare `time` module reachable without an explicit `use`. The real collision is
this package's own self re-export:

`src/lib/nogc_sync_mut/game2d/__init__.spl:17`:
```
use std.nogc_sync_mut.game2d.time as time
...
export time
```

Any sibling module inside `src/lib/nogc_sync_mut/game2d/**` (e.g.
`app/run.spl`, `loop/driver.spl`) that also wrote
`use std.nogc_sync_mut.game2d.time.det_guard as time` collided with that
package-level export named `time`, and interpreter/HIR import resolution
picked neither binding correctly, surfacing as "variable `time` not found".

This is interpreter/HIR-core-adjacent resolution logic, not application code:
it lives only in the Rust seed
(`src/compiler_rust/compiler/src/hir/lower/import_loader.rs`,
`.../hir/lower/module_lowering/module_pass.rs`, and
`src/compiler_rust/compiler/src/interpreter_module/*`). `src/compiler/`
(the self-hosted pure-Simple compiler) has no equivalent module/alias
resolution implementation to fix — confirmed by search (no
`imported_symbol_local_name` or equivalent alias-vs-builtin precedence logic
under `src/compiler/`); the only self-hosted-looking reference
(`compiler.hir.hir_lowering.imported_symbol_local_name`, exercised by
`test/03_system/compiler/compiler_import_alias_resolution_spec.spl`) is a
Rust-seed intrinsic binding exposed to specs, not `.spl` source.

## Fix shape: (a) — already resolved, no code change needed

Re-testing the doc's exact repro against the current seed
(`bin/simple run`, i.e. `bin/release/x86_64-unknown-linux-gnu/simple`) no
longer reproduces the bug in any of three shapes tried:

1. The doc's exact standalone repro (`use ... det_guard as time` +
   `time.set_deterministic_mode(true)`) — now prints `ok`, no error.
2. The same repro placed as a sibling file directly inside
   `src/lib/nogc_sync_mut/game2d/` (i.e. genuinely alongside
   `game2d/__init__.spl`'s `export time`) — also prints `ok`, no error.
3. Confirmed there is no bare/implicit `time` global reachable without an
   explicit `use` (`time.now()` with zero imports correctly fails with
   "Function 'now' not found", not a silent wrong-module hit) — rules out a
   true stdlib-builtin-name collision as the mechanism; it was always the
   package self-export above.

No commit in this session touched module/import/alias resolution. The most
likely upstream fix, based on commit history in the affected files between
the bug date and today, is `25b46777171` "fix(hir): isolate directory
sibling imports" (landed 2026-08-04), alongside several other interpreter
module-global/import-provenance hardening fixes landed 2026-07-24 through
2026-08-04 (`9cfb9e15d56`, `07adf0c25f4`, `cc5c7fa8ac4`,
`972dee3fe0c`). None of these were made as part of this investigation —
they were pre-existing, unrelated landings that incidentally closed this
defect as a side effect.

A durable regression fixture was added:
`test/fixtures/repro/game2d/game2d_time_alias_shadow_repro.spl` (mirrors the
doc's exact repro; run with `bin/simple run
test/fixtures/repro/game2d/game2d_time_alias_shadow_repro.spl` — expected
output `ok`, no "variable not found" error).

The existing `det_time` workaround in
`src/lib/nogc_sync_mut/game2d/app/run.spl` and
`src/lib/nogc_sync_mut/game2d/loop/driver.spl` was left untouched — both
files have since moved to item-level imports
(`use ... det_guard.{set_deterministic_mode, enter_callback, leave_callback}`)
rather than a whole-module `as det_time` alias, so there is nothing to
revert; reverting to a module alias is optional polish, not required, and
was not done to avoid unnecessary churn in files a concurrent session may
also be touching.
