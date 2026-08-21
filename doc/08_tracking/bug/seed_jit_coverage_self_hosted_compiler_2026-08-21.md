# Seed JIT coverage on the self-hosted compiler: the premise was wrong — there is no per-function fallback

**Date:** 2026-08-21
**Status:** OPEN (census landed; both blockers filed as follow-ups)
**Related:** `seed_interpreter_raw_throughput_2026-08-21.md` (d2181a9afe8),
`lint_dejits_whole_program_span_struct_collision_2026-08-18.md`

## The claim under test

`seed_interpreter_raw_throughput_2026-08-21.md` states that `bin/simple run` is a
**hybrid**: `compiler/src/compilability.rs` classifies each function and routes it
to Cranelift JIT (~10-25 ns/op) or to interpreter fallback (~100-1000 ns/op) by
`FallbackReason`. The proposed work was to measure which `FallbackReason`s cover
the most executed time in the self-hosted compiler and widen Cranelift lowering
for the top one or two.

**That premise is false for this lane, and the proposed work would have been
worthless.** There is no per-function split on the path `bin/simple lint` takes.
Every de-JIT here is **whole-module and whole-program**, and
`compilability::analyze_module` is never called at all.

## Evidence

`compilability::analyze_module` has exactly three non-test call sites, all in
`compiler/src/pipeline/execution.rs` (:564, :716, :961), all
`CompilabilityMode::AotNative` — the `compile --native` lane. The JIT run path,
`driver/src/exec_core.rs::run_file_jit`, calls `apply_hybrid_transform` **only**
for unresolvable externs (:1109); it never consults the classifier. So no
`FallbackReason` is ever computed for `bin/simple run`/`lint`.

Instrumented with the new census (below), a real
`lint src/compiler/80.driver/driver_types.spl` emits exactly **one** line — one
decision for the whole program, not a per-function histogram:

| lane | census output |
|---|---|
| default | `de-jit whole-module reason=cli-args-substring path=src/app/cli/lint_entry.spl` |
| `SIMPLE_EXECUTION_MODE=jit` | `de-jit whole-module reason=jit-compile-error path=src/app/cli/lint_entry.spl` |

There is no top-20 fallback-function table and no reason histogram to report,
because neither exists on this lane. A census keyed on `FallbackReason` would
have measured a code path that never executes.

## The two real blockers, in series

**Gate 1 — `cli-args-substring` (`exec_core.rs::interpreter_preference_reason`).**
`should_prefer_interpreter_for_source` diverts a source to the interpreter
*before the JIT is ever attempted* when the **entry file text contains** any of
`get_cli_args`, `rt_cli_get_args`, `sys_get_args`, `rt_get_args`, or `std.cli`.
`src/app/cli/lint_entry.spl:6` is `use std.cli.cli_util (get_cli_args)`. Every
pure-Simple CLI app parses argv, so **essentially the entire self-hosted compiler
surface is diverted by a substring match**. It is a plain `source.contains`, not
a semantic check, and it inspects only the entry file, never imports.
Escape hatch: setting `SIMPLE_EXECUTION_MODE` at all bypasses it (:1415).

**Gate 2 — `jit-compile-error`, the duplicate `Span` struct.** With gate 1
bypassed, HIR lowering fails outright:

```
HIR lowering error: Cannot infer field type: struct 'Span' field 'end_pos'
  (declared fields: start, end, line, col, file, length) [in src/app/cli/lint_entry.spl]
  ... whole module dropped to the interpreter (expect ~100-1000x slowdown).
```

Two `Span` structs collide in the flattened import namespace:

- `src/compiler/00.common/diagnostics/span.spl:7` — `start, end, line, col, file, length`
- `src/compiler/10.frontend/core/lexer_types.spl:12` — `start, end_pos, line, col`

`load_module_with_imports` flattens every import into one bare-name namespace, the
diagnostics `Span` wins, and every `.end_pos` in the lexer fails inference.

The duplicate-struct sidecar (`SIMPLE_JIT_DUP_STRUCT_FEED`,
`resolve_duplicate_global_field_variant`) is **not** the fix and is correctly
gated off. Its resolution is by field-name agreement across variants, with no
receiver type: `length` matches only the diagnostics variant, so it resolves to
index 5, and a lexer `Span` receiver (4 fields) then reads slot 5 as garbage.
That is the documented miscompile in `exec_core.rs:1030-1053`. Name-based
resolution cannot be made sound without receiver types.

Gate 2 is not unique to lint — `info` hits a *different* whole-module HIR error
(`cannot resolve import app.package.registry.config`), so each entry point has
its own blocker. This is a chain, not one bounded fix.

## What landed

`driver/src/exec_core.rs`: a level-gated de-JIT census, `SIMPLE_JIT_COVERAGE=1`,
default off. `should_prefer_interpreter_for_source` is split into
`interpreter_preference_reason` (returns the *named* reason) plus a reporter;
markers also fire on `jit-compile-error` and `jit-panic`. Previously gate 1 fired
with **no diagnostic at all**, which is exactly why this cost sat unmeasured —
the `[jit-fallback]` warning only prints when the JIT was actually attempted.

Three mechanism tests pin the reason strings (`..._names_the_cli_args_substring_gate`,
`..._is_none_for_an_ordinary_source`, `..._distinguishes_the_shs_gate`). The first
fails pre-fix: `interpreter_preference_reason` did not exist and the gate returned
a bare bool, so the reason could not be asserted.

## Follow-ups (not done here)

1. **Rename the lexer `Span` to `LexSpan`** in `src/compiler/10.frontend/core/`.
   Scope: 19 `.spl` files mention `end_pos`/`lex_span_*`; 26 files under
   `10.frontend` reference `Span`. This is the only *sound* fix for gate 2 and is
   a `src/compiler` change, so it belongs to the parser lane.
2. **Replace gate 1's substring test** with a real check, or make `get_cli_args`
   JIT-safe. Until gate 2 is cleared this changes nothing measurable, so it should
   be sequenced second.
3. Only after both: revisit whether a per-function `FallbackReason` census is
   worth building. It is inert until a module survives HIR lowering.

## Wall time (secondary — box loaded, ~44s user either way)

`lint src/compiler/80.driver/driver_types.spl`: 2m12s default, 1m26s with
`SIMPLE_EXECUTION_MODE=jit` — but the latter still ends in the interpreter after a
failed JIT attempt, so the difference is scheduling noise on a contended box, not
a JIT win. The census delta is the primary evidence; no JIT speedup was obtained,
because no module was successfully JIT-compiled.
