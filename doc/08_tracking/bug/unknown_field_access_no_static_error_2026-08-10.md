# Unknown struct/class field access: no static error, silent phantom-field write

**Status:** OPEN — blast radius unquantified; hard-error decision deferred to user
**Found:** 2026-08-10, investigating regression from `ca750206e0c7` (BoxGeometry refactor
nested `margin_top` into `spacing: BoxModel`; stale `geo.margin_top` reads/writes shipped
with no diagnostic, specs went 9/9 -> 6/9 with only assertions catching it).

## Measured behaviour (seed `bin/release/x86_64-unknown-linux-gnu/simple`, 29577536 B, 2026-08-09)

| Case | Engine | Result | Diagnostic | Exit |
|---|---|---|---|---|
| struct read `g.missing` | interp (`run`) | aborts at that line | runtime `error: semantic: class 'Geo' has no field named 'missing'` | **0** |
| class read `c.missing` | interp | same | same runtime error | **0** |
| nested / list-element read | interp | same | same | **0** |
| struct **write** `g.missing = 99` | interp | **silently CREATES the field**; readable back as 99 | **none at any level** | 0 |
| enum member read `e.missing` | interp | returns raw garbage `<value:0x1800000007>` | none | 0 |
| any of the above | JIT (`run`, default) | HIR lowering error `cannot infer field type` -> **whole module silently drops to interpreter** | `[jit-fallback]` warning only | 0 |
| same, `SIMPLE_JIT_STRICT=1` | JIT | refuses to run | hard error printed | **0** (known `jit_run_exits_zero`, ARCHITECTURAL-OPEN) |
| read inside spec | `bin/simple test` | example FAILS (runtime error at assertion time) | spec failure only | **0** |
| lint | `lint-cached` / `bin/simple lint` | **CLEAN** on silent phantom write | none | 0 (fail-open) |
| AOT | `native-build` | lane unreachable (interpreted worker exceeds budget on saturated host) | — | — |

## Root cause / where the check belongs
There is NO static field-resolution check. Detection exists only in (a) seed HIR
lowering (`src/compiler_rust/compiler/src/hir/lower/expr/access.rs`, "cannot infer
field type"), which fails OPEN by falling back to the interpreter, and (b) the
interpreter's runtime access path ("has no field named"), which never fires for
writes because interp struct/class instances are open dictionaries — writes create
phantom fields. `src/compiler/35.semantics` has no unknown-field lint. The check
belongs in 35.semantics (static, both engines) or as a lint rule; making HIR
lowering's existing detection a hard error would also need seed rebuild + the
exit-code bug fixed to be enforceable.

## Relation to `to_i64`-returns-0 (`4a6e10e27af`)
Independent code paths (runtime conversion contract vs field resolution), but the
same fail-open policy shape: "produce a plausible default / keep running" instead
of rejecting. Blast radii do NOT combine mechanically.

## Blast radius — NOT quantifiable with current tooling
The only automated detector (JIT-lowering fallback message) does not fire under
`bin/simple test` (control probe: fires under `run`, count 0 under `test` for the
same file), so counting hits over the spec corpus is vacuous. A run of
`test/01_unit/compiler` showed 0 hits — vacuously. Quantifying requires either
implementing the static check and sweeping, or a per-module `run`-path lowering
sweep. Until that number exists, do not flip this to a hard error.
