# ast_reset() runs INSIDE the transient array scope, so the flat-AST arena is freed under its readers

- **Id:** ast_arena_reset_inside_transient_scope_2026-08-01
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  the 6,474-event Stage 4 signature did **not** reproduce at
  `ca8ff9e003d2` (see "Reproduction status" below), so the fix is a proven-real
  hazard closure, not a demonstrated before/after on that signature.
- **Severity:** blocker — aborts Stage 4 phase 3 (HIR lowering) and voids every
  unresolved-type/name/import census taken from such a run
- **Signature:** `[stmt_get_tag] OOB idx=<n> arena_len=0 arena_gen=<gen> -> -1`
  and `[flat-bridge] missing stmt tag idx=<n> tag=<t>`, ending in
  `[ERROR] phase 3 FAILED`
- **Guard that already treats it as fatal:** `scripts/bootstrap/bootstrap-from-scratch.sh:1617`
  (must NOT be weakened)

## Symptom

A genuine Stage 4 build (`bootstrap_native_build_main` env/flags) emitted 6,474
`[stmt_get_tag] OOB` / `[flat-bridge] missing stmt tag` events over 1,213
distinct `.spl` files and died with `[ERROR] phase 3 FAILED` after 24:46 wall /
1477.89 s user CPU / 1.44 GB peak RSS. Many events carried `arena_len=0` against
live arena generations in the 591–2409 range: the generation counter was
advancing normally while the statement arena reported *zero* entries.

Because phase 3 is where unresolved-type/name/import diagnostics are emitted,
the run's `unresolved type/name/import = 0` line is an **early-abort artifact**,
not a clean census.

## Root cause (PROVED)

Two independent proofs, code and execution.

### 1. The runtime contract

`src/runtime/runtime_native.c`:

- `rt_core_register_scoped_immortal()` (~line 951) stamps **every** array, dict,
  enum, closure and float created while `rt_core_transient_array_scope_active`
  and not paused with the live scope id, and tracks it.
- `rt_transient_array_scope_end()` (~line 1114) calls
  `rt_core_reclaim_transient_immortal(scope_id)` (~line 1418), which for every
  tracked object with that scope id **erases it from the immortal pointer
  registry**, `free()`s `->data`, and `free()`s the object.
- Every array accessor resolves through `rt_core_array_ptr()` →
  `rt_core_as_array()`, which returns `NULL` for a pointer that is not in the
  registry. So after reclamation, for any still-held reference:
  - `rt_array_len()` → no length (0 in `runtime_native.c`, `-1` in the frozen
    stage3 `libsimple_runtime.a`),
  - `rt_array_push()` → returns 0, the push is **silently dropped**,
  - `rt_array_clear()` → returns 0, **silent no-op**,
  - `rt_array_get()` → nil sentinel.

The death is silent and permanent. There is no crash and no diagnostic.

### 2. The compiler parks process-lifetime state in that scope

`src/compiler/80.driver/driver_source_pipeline_parsing.spl`:

```
pub fn driver_end_transient_parse_scope() -> bool:
    lexer_release_parse_source_globals()
    ast_reset()                      # <-- allocates, scope still ACTIVE
    rt_transient_array_scope_end()   # <-- frees what ast_reset just allocated
```

`ast_reset()` is not a pure clear. It re-allocates process-lifetime arena state:

- `ast_module_decl_slots_clear()` (`_Ast/decl_nodes.spl:1305`) was an
  **unconditional** `module_decl_slots = []` — a fresh array on *every* reset,
  therefore a fresh scope-owned array on every file;
- every `if X == nil: X = []` guard in `ast_reset` / `expr_reset` /
  `stmt_reset` / `_ast_slots_ensure` fires in native binaries, which
  zero-initialise module arrays.

So each per-file scope teardown freed arena globals that the *next* file's parse
and the HIR lowering phase still referenced. Once dead, the arena could never be
refilled (`push` dropped, `clear` no-op) while the parallel counters
(`stmt_count_slot`, `ast_gen_slot`) kept advancing — producing exactly
"index N against `arena_len=0` at generation 591–2409".

`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:722` had the same
inverted order.

### Empirical proof

A standalone C probe against the frozen stage3 runtime
(`libsimple_runtime.a`, sha `9fe5e077…`) reproduces it in under a second:

```
control len before scope    = 2      (allocated OUTSIDE the scope)
arena len inside scope      = 2
arena len after scope end   = -1
arena push after scope end  = 0 (len still -1)
arena clear after scope end = 0
control len after scope end = 2      (CONTROL unaffected -> not vacuous)
```

This is now pinned as a permanent contract case in
`src/runtime/test/rt_transient_heap_scope_selfcheck.c` (8 assertions, with the
outside-the-scope CONTROL array so it cannot pass vacuously).

## Fix

1. `_Ast/decl_nodes.spl` — `ast_module_decl_slots_clear()` clears **in place**
   instead of rebinding `= []`, removing the only unconditional per-reset
   allocation (and the matching per-reset array leak).
2. `driver_source_pipeline_parsing.spl` — `driver_end_transient_parse_scope()`
   ends the transient scope **before** `ast_reset()`, so the reset's allocations
   are born outside any scope and stay process-immortal. The per-file parse
   garbage the scope genuinely owns is still reclaimed exactly as before.
3. `_FlatAstBridge/module_assembly.spl` — same reordering in
   `parse_and_build_module_scoped()`.
4. `src/runtime/test/rt_transient_heap_scope_selfcheck.c` — contract case
   pinning the silent-death behaviour so any new
   `rt_transient_array_scope_begin()` call site inherits the warning.

The diagnostic itself is untouched: those 6,474 events are the only reason this
was visible, and `bootstrap-from-scratch.sh:1617` still treats the signature as
fatal.

## Family

This is the statement/arena-side member of a known systemic weakness in
generation/reset discipline:

1. `expr_reset` clears the AST arrays but never unsets the env mirror, so stale
   indices answer from the previous compilation unit and the bounds guard is
   unreachable in exactly the mode that needs it.
2. A reset placed in a pipeline entry point is not a reset
   (`_llvm_bootstrap_string_global_text` reset only in `translate_module`, which
   the bootstrap object emitters bypass).
3. `parse_module_silent_checked` does not reset between calls, so per-file
   verdicts are order-dependent.

This one is the mirror image of (2): the reset is in the right *function* but on
the wrong side of a lifetime boundary. **A reset that runs inside a scope that is
about to be torn down is not a reset — it is an allocation into a grave.**

## Verification

- Runtime contract: `rt_transient_heap_scope_selfcheck` — 8 new assertions pass;
  the single pre-existing failure ("promoted nested array and boxed float
  survive") reproduces identically with the **unmodified** file against the same
  frozen stage3 `libsimple_runtime.a`, so it is not attributable to this change
  and is tracked separately.
- Acceptance criterion for closing this bug: a Stage 4 native build that reaches
  the **end of phase 3**, with the unresolved-type/name/import counts reported
  from that run. Not "fewer OOB events".

## Reproduction status and the phase-3 census (PROVED)

A full Stage 4 native build was run with the exact `bootstrap_native_build_main`
env and flags, using the frozen 154 MB `stage2-runtime-authority` compiler,
against the shared working copy at `ca8ff9e003d2`:

```
VERDICT= tag=full1 exit=1 secs=1522 stmt_oob=0 flat_stmt_miss=0
         expr_oob=0 flat_expr_miss=0 phase3_FAILED=0 outbin=no
```

Two findings, both load-bearing:

1. **The 6,474-event signature did NOT reproduce.** Zero `[stmt_get_tag] OOB`,
   zero `[flat-bridge] missing stmt tag`, zero `[ERROR] phase 3 FAILED`. So the
   fix in this commit cannot be credited with clearing that signature — it closes
   a hazard proved real at the runtime level, on the code path that produced it,
   but the failing revision (`ecf13e1cf3f8`) is not reachable from origin and the
   defect did not reproduce at `ca8ff9e003d2`.

2. **Phase 3 completed.** The run proceeded past HIR lowering all the way into
   LLVM codegen and failed there, on a *different* defect — two files rejected
   with `llvm codegen: semantic: llvm global load referenced undeclared symbol`:
   - `src/compiler/20.hir/hir_lowering/module_surface.spl` — symbol `interp_list`
   - `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
     — symbol `animation_time_ms`

   That is now the Stage 4 blocker, and it is downstream of phase 3.

Unresolved census from that run (the first such census taken from a build that
demonstrably did NOT abort in phase 3):

| diagnostic | count |
|---|---|
| `unresolved type` | 0 |
| `unresolved name` | 0 |
| `unresolved import` | 0 |
| `unresolved method` | 0 |
| `unresolved symbol` | 0 |
| `unresolved call` | 2 (`platform_normalize`, emitted during codegen) |

### Post-fix run (regression check)

A second full Stage 4 build, same env/flags and same frozen compiler, against the
fixed tree (origin `a0d20a0` plus this commit's changes):

```
VERDICT= tag=fixed exit=1 secs=1379 stmt_oob=0 expr_oob=0 flat_stmt_miss=0
         flat_expr_miss=0 phase3_FAILED=0 unresolved_type=0 unresolved_name=0
         unresolved_import=0 unresolved_call=2
```

**No regression:** phase 3 completes, the arena signature stays at zero, and the
run is 143 s faster than the baseline. It fails at the same LLVM-codegen stage.

The fixed run reports **1** failed file (`animation_time_ms`) where the baseline
reported **2** (`animation_time_ms` + `interp_list` in
`src/compiler/20.hir/hir_lowering/module_surface.spl`). **This is CONFOUNDED and
must not be read as an improvement from this fix:** the two runs used different
source trees, and `module_surface.spl` itself differs between them
(`0d02867e22de8636` vs `9e6b79538377b310`). The renderer file that fails in both
is byte-identical in both trees (`488351d2a8fc6ee9`), which is the consistent
control. A clean before/after needs both arms built from the *same* tree.

Note also `phase3_file_start=0` / `phase3_file_done=0` in the fixed verdict: the
`log_phase` markers are not routed to this log at all, which independently
confirms the caveat below — the census zeros are absence-in-this-log, not a
verified diagnostic channel.

**Caveat, stated explicitly:** the whole build produced only a 10-line log, so
these zeros mean "no such diagnostic reached this log", not "the phase 3
diagnostic channel was verified to be live". They are no longer *early-abort*
artifacts — the run reached codegen — but a lane that needs a positively
verified census should re-run with the phase-log knobs on and assert a positive
marker (e.g. `phase3:hir:file:done` counts) rather than reading absence.

## Notes / traps for the next lane

- Small multi-unit builds do **not** reproduce it: a 3-file build with the exact
  Stage 4 flags is clean. The defect needs the streaming-surface path to open and
  close many scopes.
- `[stmt_get_tag] OOB` appearing on log line 1 is partly a **buffering artifact**:
  `print` goes to block-buffered stdout while other phases write elsewhere, so
  log line order is not chronological order. Do not infer "it failed first" from
  the line number.
- The frozen 154 MB `stage2-runtime-authority` copy is the compiler to use. The
  shared seed at `src/compiler_rust/target/bootstrap/simple` has been observed
  mid-rebuild at 32 MB with no LLVM.
