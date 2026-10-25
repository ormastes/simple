# Transient promotion misses texts held by their untagged data pointer (2026-10-25)

## Symptom
Phase 3 Stage 3 (`S/r27/stage3/simple.pu6`), hello world, worker AND in-process
route: `phase 3 FAILED ... HIR lowering error in src/app/zz_r27_t/h.spl:
unresolved name: =0 task_done=1 task_total=6 elapsed_ms= at :0:0`. The
identifier text is bytes of a later `[build]` progress line.

## Root cause
1. **Real bug (compiler/codegen):** `expr_get_str` (`src/compiler/10.frontend/core/_AstExpr/accessors.spl:207`)
   returns an UNTAGGED `char*` into a transient `RtCoreString`'s data
   (Stage-2-compiled text decode via `rt_interp_cstr`): gdb at its `ret`
   showed x0 = `0x...d700`, x2 = `0x...d6f0` (the string header, magic
   `STR1`, reserved=2 TRANSIENT, len 5, "print"). ParserModule fields store that
   raw pointer.
2. **Why it frees:** `rt_core_transient_classify` (runtime_native.c) only knows
   tagged heap values and raw allocation bases, so the word classifies as "not
   heap" and promotion silently skips it (no refusal, so
   `SIMPLE_TRANSIENT_PROMOTE_DEBUG` prints nothing). A hardware watchpoint on
   the "print" string header fired in `free()` from
   `rt_transient_array_scope_end <- driver_end_transient_parse_scope <-
   parse_full_frontend_selected_v1`.

## Workaround (this change, runtime C)
`rt_core_transient_classify`: an untagged word `w` whose `w - offsetof(RtCoreString, data)`
is a REGISTERED transient, non-shared `RtCoreString` classifies as that
string. Membership (`rt_core_is_registered_immortal_ptr`, a pointer-only hash
lookup) is checked before any dereference, so an arbitrary aligned word is never
read. Tagged with `@workaround`.

Evidence: `src/runtime/test/rt_transient_heap_scope_selfcheck.c`
`check_raw_text_data_pointer_promotes` fails on the unpatched runtime
("text reached only by its data pointer survives") and passes patched. Evidence build: the capsule flag set incl. `-DSIMPLE_RUNTIME_MEMORY_OWNER=1 -DSIMPLE_CORE_C_STANDALONE=1` (S/r27/bp/rt/flags.txt); the non-OWNER `#else` arm is structurally covered but not run. Stage 3
hello world then passes HIR lowering (post-lowering count=0) and stops at the
next blocker (hc_enc_hir_module SEGV).

## Open
- Compiler fix: text values read from arrays/dicts must stay tagged handles
  (no raw `char*` in stored struct fields). Takes effect once Phase 3 rebuilds itself.
- Rust runtime twin (`src/compiler_rust/runtime/src/value/collections.rs`
  `rt_transient_heap_promote` walker) has no equivalent rule. No new `rt_*`
  symbol is added, so the dual-implementation ratchet does not change; parity
  for the Rust lane is a follow-up.
