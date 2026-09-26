# Stage 2 admission SIGILL: unguarded `lex_env_save_enabled[0]` read in the lexer

- **Filed:** 2026-09-26
- **Status:** FIXED (defensive guard landed) — see "What was NOT re-verified" below
  for the part of this record that is a hypothesis, not an observed fact.
- **Area:** `compiler.frontend.core.lexer`, native codegen module-level state
- **Host:** yoon-note, x86_64-unknown-linux-gnu

## Symptom (given, not re-derived here)

A prior gdb session on the stage-2 candidate binary
(`.simple/storage/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority/simple`)
produced this fully symbolized backtrace for the `rc=132` (SIGILL)
`candidate_frontend_smoke: hello-world-positional-build failed` failure tracked
in
`doc/08_tracking/bug/stage2_candidate_env_get_infinite_recursion_sigill_2026-09-26.md`:

```
Program received signal SIGILL, Illegal instruction.
#0  compiler.frontend.core.lexer.current_core_lexer_save ()
#1  compiler.frontend.core.lexer.lex_next ()
#2  compiler.frontend.core.lexer.lex_next_snapshot ()
#3  compiler.frontend.core.parser.parser_advance ()
#4  compiler.frontend.core.parser.parser_init_with_path ()
#5  compiler__frontend___FlatAstBridge__module_assembly__parse_and_build_module_scoped ()
#6  compiler.frontend.frontend.frontend_parse_or_restore ()
```

## Structural cause (confirmed by source inspection)

`src/compiler/10.frontend/core/lexer.spl` keeps `lex_env_save_enabled: [bool]`
as a module-level array (`var lex_env_save_enabled: [bool] = [false]`,
originally at `:63`). `lex_init_with_path` already carries a defensive guard
for exactly this array before writing it:

```
if lex_env_save_enabled.len() == 0:
    lex_env_save_enabled = [false]
...
lex_env_save_enabled[0] = (env_get_nullable("SIMPLE_BOOTSTRAP_LEX_ENV_SAVE") ?? "") == "1"
```

— evidence someone already hit the empty-array case here once. But every READ
site indexed `[0]` directly with no length check: `lex_cur_kind_set`,
`lex_cur_line_set`, `lex_cur_col_set`, `lex_cur_text_set`,
`lex_cur_suffix_set` (5 setters), `current_core_lexer_save` (frame #0 above),
and `lex_next` itself (`val env_save = lex_env_save_enabled[0]`) — 7 unguarded
reads total, only 2 of which (`current_core_lexer_save`,
`lex_next`) were named in the initial report; the other 5 share the identical
pattern and were fixed in the same change.

This file's own header states: "Design: All state in module-level vars...
Works when compiled to C; NOT in the interpreter (closure bug)." — module-level
array semantics under native codegen are a known-fragile spot in this exact
file (see also `doc/08_tracking/bug/simple_module_const_scalars_need_runtime_init_on_baremetal_2026-09-19.md`
for the general defect class: module-level values land in `.bss` and are
filled by a generated `__module_init_*` a given consumer may never call). An
unguarded `[0]` read on an array that is legitimately empty at that point in a
natively-compiled call graph is a textbook out-of-bounds trap.

## What was NOT re-verified in this session

Live reproduction of the exact SIGILL was attempted but not achieved directly:

- The task's literal narrow reproducer
  (`SIMPLE_BOOTSTRAP=1 SIMPLE_SCV_FREEZE_FALLBACK=1 native-build
  scripts/check/cert/redeploy_gate/fixtures/hello_world.spl -o /tmp/x.bin`)
  already returns **rc=0** on this tree, because the unrelated `io_runtime`
  `host_os()` recursion fix in
  `stage2_candidate_env_get_infinite_recursion_sigill_2026-09-26.md` (uncommitted,
  already present in this working tree) independently resolved that exact
  narrow command.
- Reproducing the FULL sanitized-environment admission probe (the
  `bootstrap-from-scratch.sh` env scrub: unset every var except
  `HOME`/`TMPDIR`/`PATH`/`LC_ALL`/`LANG`) on this host instead surfaced a
  **different, unbounded memory-growth condition**: the candidate binary
  spends 4+ GB and does not return within 90-150s just bootstrapping its own
  ~600-file compiler closure under `SIMPLE_LIB`, well before it ever reaches
  `current_core_lexer_save` for the target fixture (confirmed by a one-shot
  `eprint` placed at that exact line, under a `ulimit -v` memory cap: it never
  printed before the process aborted on the cap). This matches
  `stage2_candidate_env_get_infinite_recursion_sigill_2026-09-26.md`'s own
  "Post-fix state" section ("Stage 2 admission is STILL RED... which specific
  variable flips the outcome has NOT been identified"). Two live attempts at
  this reproduction on this 7.4 GiB host grew to several GB RSS before being
  killed; do not repeat this without a tight `ulimit -v` and a foreground
  `timeout -s KILL`, per `.claude/memory/oom-run-capped-mandatory.md`
  (`run_capped.shs`'s `systemd-run --user --scope` detaches from the caller's
  process group and does NOT get killed by a wrapping `timeout`, which was
  independently rediscovered here and cost a manual `pkill` twice).
- Net effect: the SIGILL backtrace above is trusted as given (per the task
  framing), and the fix here is verified **structurally and by a targeted unit
  spec** (see below), not by re-triggering the exact native trap live. Whether
  fixing this array closes stage-2 admission fully, or whether the separate
  unbounded-bootstrap-memory issue above is the thing actually gating
  `run-phase1-local.shs`, is unresolved and is a distinct, still-open question
  from this record.

## Fix

`src/compiler/10.frontend/core/lexer.spl`: added a small pure helper and a
zero-arg accessor, and routed every unguarded read through it:

```
fn bool_slot0_or(slot: [bool], default: bool) -> bool:
    if slot.len() == 0:
        return default
    slot[0]

fn lex_env_save_on() -> bool:
    bool_slot0_or(lex_env_save_enabled, false)
```

All 7 call sites (`lex_cur_kind_set`, `lex_cur_line_set`, `lex_cur_col_set`,
`lex_cur_text_set`, `lex_cur_suffix_set`, `current_core_lexer_save`,
`lex_next`) now call `lex_env_save_on()` instead of indexing
`lex_env_save_enabled[0]` directly.

## Specs

- `test/01_unit/compiler/frontend/lexer_env_save_slot_empty_array_guard_spec.spl`
  — reproducing: `bool_slot0_or([], default)` must return `default`, not trap.
  Verified to FAIL (`array index out of bounds`) against the unguarded
  `slot[0]` body and PASS with the guard.
  Generalization: `bool_slot0_or` on a populated slot is unchanged, and
  `lex_env_save_on()` composes safely across a real `lex_init`/`lex_next`
  session.

## Related

- `doc/08_tracking/bug/stage2_candidate_env_get_infinite_recursion_sigill_2026-09-26.md`
  — the `io_runtime` `host_os()` recursion (fixed) and the still-open
  sanitized-env "still red" state this record's reproduction attempt
  independently reconfirmed.
- `doc/08_tracking/bug/simple_module_const_scalars_need_runtime_init_on_baremetal_2026-09-19.md`
  — the general module-level-init defect class this fix defends against.
