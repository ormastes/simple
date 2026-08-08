# Lane SLICE/ARRIDX — `[T].index_of(v)` returns -1 for a PRESENT element

Bug id used by the Rust-side lane: `array_index_of_always_minus_one_2026-07-28`.

## Contract (unchanged, deliberately)
Array `index_of` returns a plain `i64` with `-1` as the not-found sentinel —
identical to `text.index_of`. It is NOT an Option. Guard with `>= 0`.
`text.index_of` was NOT touched (28 files were just repaired against its
`>= 0` contract).

## THE SPLIT: `bin/simple run` is broken, `bin/simple test` is correct

Same binary, same expression, opposite answers. Proven with a two-sided
discriminator spec (A asserts `==0`, B asserts `==-1`):

| harness | `[10,20,30].index_of(10)` |
|---|---|
| `bin/simple run` (and `SIMPLE_NO_JIT=1 bin/simple run`) | **-1 — WRONG** |
| `bin/simple test` (sspec harness) | **0 — correct** (A ✓, B ✗) |

`bin/simple test` drives the seed's **interpreter**
(`interpreter_method/collections.rs:248`), which has a correct array
`index_of`. `bin/simple run` drives the seed's **codegen/JIT**, whose method
tables map `index_of` → `rt_string_find` unconditionally. `SIMPLE_NO_JIT=1` did
NOT move `run` onto the interpreter — it produced byte-identical broken output,
so it is not a usable A/B knob for this defect.

Consequence for verification: **a green sspec run does NOT clear this bug.**
Any spec for array `index_of` passes today purely because the harness takes the
one path that was never broken. The truth table below (from `bin/simple run`) is
the one that reflects shipped behaviour.

## Truth table — `bin/simple run` (Rust bootstrap seed, built 2026-07-27 22:06)
DEFAULT and `SIMPLE_NO_JIT=1` produced IDENTICAL rows.
Repro: `build/arridx_1/repro3.spl`.

| case | expected | DEFAULT (JIT) | SIMPLE_NO_JIT=1 (interp) |
|---|---|---|---|
| `[i64]` present first  | 0  | **-1 FAIL** | **-1 FAIL** |
| `[i64]` present mid    | 2  | **-1 FAIL** | **-1 FAIL** |
| `[i64]` present last   | 2  | **-1 FAIL** | **-1 FAIL** |
| `[i64]` absent         | -1 | -1 pass | -1 pass |
| `[i64]` empty          | -1 | -1 pass | -1 pass |
| `[text]` present first | 0  | **-1 FAIL** | **-1 FAIL** |
| `[text]` present last  | 1  | **-1 FAIL** | **-1 FAIL** |
| `[text]` absent        | -1 | -1 pass | -1 pass |
| `[struct]` present     | 0  | **-1 FAIL** | **-1 FAIL** |
| `[struct]` absent      | -1 | -1 pass | -1 pass |
| duplicates, first occ  | 0  | **-1 FAIL** | **-1 FAIL** |
| `text.index_of("h")`   | 0  | 0 pass | 0 pass |
| `text.index_of("llo")` | 2  | 2 pass | 2 pass |

Every PRESENT element reports absent; every ABSENT case is accidentally right.
`text.index_of` is unaffected — the not-found sentinel is a red herring, the
defect is that the array search never runs at all.

## Root cause (two independent trees, same shape)

`index_of` was dispatched to the **string** search for every receiver kind.
`contains` had already been made receiver-polymorphic; `index_of` never was.

1. **Rust seed, CODEGEN path only** (`bin/simple run`) —
   `codegen/instr/calls.rs`, `closures_structs.rs`, `llvm/emitter.rs`,
   `llvm/functions.rs` mapped `"index_of"` unconditionally to `rt_string_find`.
   `rt_string_find` bails to -1 on a non-string receiver, so every array call
   returned -1. `rt_array_index_of` existed and was correct but was never wired
   in. The seed's *interpreter* (`interpreter_method/collections.rs:248`) always
   had a correct array arm — hence the run/test split above.
2. **Self-hosted (pure-Simple)** — `eval_array_method` had **no `index_of` arm at
   all**. Calls fell through to
   `eval_set_error("no method 'index_of' on array")`, which returns VAL_NONE
   (`-1`) and is silently swallowed (nothing on stderr). Callers read that -1 as
   "absent". The C codegen path has the same gap:
   `cg_expr.spl:527` emits `spl_str_index_of` with no `is_array_type` guard,
   unlike `contains` at `cg_expr.spl:509-517`.

## What this lane changed

**Fixed (uncontended tree):** added the missing `index_of` arm to BOTH copies of
`eval_array_method`, mirroring the existing `contains` element-equality loop and
returning the first matching index, `-1` when absent:
- `src/compiler/10.frontend/core/interpreter/eval_methods.spl`
- `src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl`

**NOT touched — CONTENDED, writeup only:** `src/compiler_rust/` has 20+ modified
files from a live place-model lane (`interpreter/place.rs` is newly added), and
that lane has *already landed* the Rust-side fix in the working tree:
`rt_index_of` in `runtime/src/value/collections.rs:3051` (array tried first,
falls back to `rt_string_find`; sound because both callees are total and return
-1 on receiver mismatch), with the codegen tables remapped to it. That fix is
**not in the deployed binary** — the binary predates it by ~2.5h, which is why
the table above is still red. It needs a seed rebuild to take effect, not
another edit. Do not re-fix it.

## Still open
`cg_expr.spl:527` (pure-Simple → C codegen, `native-build` path) still emits
`spl_str_index_of` for array receivers. There is no `spl_array_index_of` in
`src/runtime/runtime.c` (only `spl_array_contains_str`). Adding one requires a
runtime extern + bootstrap, so it was left out of this lane; native-build
`[T].index_of` is expected to still be wrong.

## Spec
`test/01_unit/language/array_index_of_spec.spl` — absolute oracles for
present-first / present-mid / present-last / absent / empty across `[i64]` and
`[text]`, plus first-occurrence-on-duplicates, index_of/contains agreement, a
text.index_of non-regression guard, and one deliberate-red calibration case
(`CALIBRATION deliberate-red -- must FAIL`) that must be seen failing or the run
did not execute.

Verdict: **14 examples, 1 failure** — the single failure is the calibration case,
exactly as designed; all 13 real oracles green. But see THE SPLIT above: the
sspec harness runs the interpreter, which was never broken, so this green is a
regression guard for the interpreter/self-hosted path only. It does **not**
witness the codegen fix. Re-run `build/arridx_1/repro3.spl` under
`bin/simple run` after the next seed rebuild — that is the real gate.

## Blast radius — genuine array receivers in owned `src/**`
1175 `.index_of(` sites total; only these have array receivers:

| site | consequence while broken |
|---|---|
| `src/lib/{nogc_sync_mut,nogc_async_mut}/dependency_tracker/graph.spl:97` | **worst.** DFS cycle extraction: `path.index_of(module)` always -1 ⇒ `cycle_start` falls back to 0 ⇒ the reported circular-dependency cycle always starts at the DFS root, so every cycle diagnostic names the wrong (over-long) cycle |
| `src/lib/nogc_sync_mut/mem_tracker/mod.spl:145` | `tags.index_of(entry.tag)` always -1 ⇒ `mem_group_by_tag` never groups: one duplicate row per entry, every count stuck at 1 |
| `src/app/cli_parser.spl:416` + `src/lib/{nogc_sync_mut,gc_async_mut,nogc_async_mut}/cli/cli_parser.spl:415` | `spec.positionals.index_of(pos) ?? -1` always -1 (the `?? -1` is also a no-op on a plain i64) ⇒ positional-argument ordering resolves wrong |

Text-receiver false positives excluded: `browser_session.spl:1022/1048/1049`,
`http_server/proxy.spl:295`, `messageActions.spl:331`.
