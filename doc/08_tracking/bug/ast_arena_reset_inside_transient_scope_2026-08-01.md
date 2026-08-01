# ast_reset() runs INSIDE the transient array scope, so the flat-AST arena is freed under its readers

- **Id:** ast_arena_reset_inside_transient_scope_2026-08-01
- **Status:** root-caused, fix landed, Stage 4 end-to-end verification pending
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
