# Flat AST Bridge: type-expr index goes stale across an interleaved `ast_reset()`

**Status:** FIXED 2026-07-12 — bounds-check added in `convert_flat_type` before the
expr-arena fallback read; falls back to `TypeKind.Infer` when the index is out
of range (restores pre-#146 behavior for the unrecoverable case).
**Severity:** Blocking — stage-4 native build of the full compiler (`native_build_main.spl`,
`--mode dynload`) dies with `error: semantic: array index out of bounds: index is 48
but length is 13`.
**Affected file:** `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl` (`convert_flat_type`, ~line 176)
**Path:** `bug` track.

## Symptom

Running the seed interpreter over the stage-4 build pipeline (parsing
`src/app/io/process_ops.spl`, which declares `extern fn ... -> (text, text, i64)`
at line 8) raised, from the Rust seed's `collections.rs:479` bounds check:

```
error: semantic: array index out of bounds: index is 48 but length is 13
```

## Root Cause

`convert_flat_type(type_expr_idx)` handles the fixed `TYPE_*` tag constants
(≈1-33) and anything `>= TYPE_UNION_BASE` as pre-resolved type tags. Any other
value (the tag-space hole between ~34 and `TYPE_UNION_BASE - 1`) is treated as
a raw index into the shared flat-AST **expr arena** and read directly via
`expr_get_tag(type_expr_idx)` → `expr_tag[idx]` (no bounds check).

For a declared `-> T` return type, that index is captured once at parse time
into `decl_ret_type[idx]` (see `decl_get_ret_type`). `convert_decl_extern_fn`
(convert_nodes.spl:1026-1029) reads it back later, when `flat_ast_to_module`
walks the decl list and converts each extern fn. If a **different** parse job
runs `parser_init_with_path` → `ast_reset()` in between (see
`src/compiler/10.frontend/core/_Ast/module_state.spl:312-420`, which calls
`expr_reset()` → `expr_tag.clear()`), the shared, module-level expr arena is
wiped and refilled with a shorter/different sequence before the stale index is
dereferenced. The arena is process-global (`_AstExpr/nodes.spl:84`,
`var expr_tag: [i64] = []`), not per-file/per-thread, and the stage-4 build
invokes the driver with `--threads 16` across multiple source roots, so a
sibling parse job resetting the arena between "index captured" and "index
consumed" is a real interleaving, not a hypothetical.

This is the same class of hazard the reviewer flagged at 7 other call sites in
`convert_nodes.spl` (lines 599, 751, 758, 887, 910, 1010, 1029) — any
`convert_flat_type` call whose index was captured before the point where it's
finally consumed is exposed whenever an intervening `ast_reset()` can occur.
The extern-fn return type (line 1029) is the one proven to trip it, introduced
by the recent #146 change that started actually threading the extern return
type through (previously discarded, so this path was dead).

When the arena happens to be **longer** after the reset (rather than shorter),
the read stays in-bounds but is **silently stale** — it reads whatever tag now
occupies that slot from the unrelated, later parse job. This is strictly worse
than the OOB crash because it produces wrong-but-plausible output instead of
failing loudly.

## Fix Applied

Investigated moving the extern-fn return-type conversion earlier (eager,
before any possible reset) per the "preferred" fix path. This is not
applicable here: `convert_decl_extern_fn` is already called as early as
architecturally possible for the *current* file — `flat_ast_to_module`'s decl
loop runs immediately after `parse_module_body()` completes for that file, and
no decl branch in the loop (`module_assembly.spl` tag dispatch) recursively
re-parses another file inline. The interleaving comes from *outside* that
scope (a sibling driver/thread parsing a different file), which eager
conversion within the same function cannot prevent — moving the call earlier
does not close the race.

Took the acceptable minimal fix instead: bounds-check `type_expr_idx` against
the live arena length (`expr_count()`, `_AstExpr/nodes.spl:188-192`) before
the `expr_get_tag` read in `convert_flat_type`, and return
`Type(kind: TypeKind.Infer, span: make_span())` when out of range — matching
the pre-#146 behavior for this decl shape.

```
src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:239-249 (approx, after edit)
    if type_expr_idx >= TYPE_UNION_BASE:
        return Type(kind: TypeKind.Named(type_tag_name(type_expr_idx), []), span: make_span())
    if type_expr_idx >= expr_count():
        return Type(kind: TypeKind.Infer, span: make_span())
    val tag = expr_get_tag(type_expr_idx)
    ...
```

## Residual Risk (documented, not hidden)

This fix only catches the **out-of-range** case. A stale-but-in-bounds read
(arena reset to a length that still covers `type_expr_idx`, now holding an
unrelated expr from a different parse job) is **not** detected or corrected by
this change — `convert_flat_type` will silently return a type built from
whatever tag/text now occupies that slot. The other 6 flagged call sites
(convert_nodes.spl:599, 751, 758, 887, 910, 1010) share the same underlying
hazard and were not touched (out of scope for this fix; each needs its own
audit of whether its captured index can outlive an intervening `ast_reset()`).

The durable fix is either (a) make the flat-AST arena per-file/per-thread
instead of process-global module state, or (b) have the driver serialize
"parse file N" with "convert file N" as one atomic unit across all worker
threads (no other thread's `ast_reset()` may run between them for the same
arena instance). Both are structural changes beyond this bug's scope.

## Secondary Finding (feature request)

The seed interpreter's array-index-out-of-bounds diagnostic
(`collections.rs:479`, `error: semantic: array index out of bounds: index is N
but length is M`) carries no call-stack/location attribution — it took manual
bisection through `convert_flat_type` to find the offending `expr_tag[idx]`
read. Request: thread `DEBUG_CALL_STACK` (or equivalent Simple-frame
attribution) into this specific Rust-side bounds-check panic path so future
OOB errors report which Simple function/line performed the indexing.

## Verification

- `timeout 120 src/compiler_rust/target/bootstrap/simple run <tiny 2-fn .spl>` — still runs correctly (prints `5`).
- `bin/simple test test/01_unit/compiler/frontend/flat_ast_if_else_bridge_spec.spl` — 3/3 pass.
- Full stage-4 gate (`native_build_main.spl --backend cranelift ... --mode dynload`,
  cache cleared first): see report for pass/fail and evidence.

## Corrected root cause (2026-07-12) — re-entrant-parse theory DISPROVEN; hang is earlier and native

A follow-up investigation (isolated worktree, seed pinned from
`src/compiler_rust/target/bootstrap/simple`) set out to prove a refined theory
for the self-host `native_build_main.spl --mode dynload --threads 16` hang:
that an **in-process re-entrant parse** (a lazy/deferred sub-parse calling
`parser_init_with_path` → `ast_reset()` from inside `flat_ast_to_module`'s
per-decl conversion loop) invalidates the still-in-flight `decl_body_stmts`
indices of the function currently being converted, producing the observed
`[flat-bridge] missing stmt tag idx=54..70 tag=-1` spin. This refined theory
correctly ruled out the *original* doc's `--threads 16` cross-thread race
(confirmed process-based via `rt_process_spawn_async`, each worker its own
address space) and cross-module interleaving (`parse_and_build_module` is
atomic: parse → convert, no reset in between, per file).

**Instrumentation added for the proof** (module-level `ast_reset_seq` counter
+ trace print in `ast_reset()` at `module_state.spl:319-326`, and
`STALE-BODY-SUSPECT`/`OOB-ABOUT-TO-HIT` prints in `convert_decl_fn` at
`convert_nodes.spl:930-940`, gated by `SIMPLE_TRACE_AST_RESET=1`) was already
present on `main` from a prior session before this investigation began — see
`git log` on `module_state.spl`/`convert_nodes.spl` (commit `007c06a056b`
"chore(sync): working-copy snapshot before gh sync"). This investigation
extended it with a `cap_seq`/`cur_seq` pair threaded from `convert_decl_fn`'s
`decl_get_body` capture site through to the `stmt_get_tag` OOB print in
`convert_flat_stmt`, to directly compare "reset count at capture" vs. "reset
count at consumption." **That extension was reverted before commit** — see
below — because the build never reaches the code it instruments.

### What was actually proven

Ran the full build 3 times (`SIMPLE_TRACE_AST_RESET=1`, `--backend cranelift
--source src/compiler --source src/app --source src/lib --entry-closure
--threads 16 --cache-dir build/bootstrap/native_cache --mode dynload --entry
src/app/cli/main.spl`, cache cleared each time; one run also wrapped in
`strace -f -e trace=openat`). All three runs **hang at the exact same point**:
stdout freezes at line 1135 (identical final line: a "Deprecated syntax for
type parameters" warning for `src/lib/nogc_async_mut/path.spl:142`), one OS
thread pegged at ~65-99% CPU in kernel `R` state (`wchan=0`, i.e. userspace
compute, not blocked on a lock), the other 4 threads parked on `futex_wait_queue`.

Two decisive facts rule out the re-entrant-parse theory for *this*
manifestation:

1. **Zero occurrences** of `[ast_reset]`, `[parser_init_with_path] resetting`,
   `[flat-bridge]`, `[convert_decl_fn]`, or `[stmt_get_tag] OOB` anywhere in
   any of the 3 logs. The traced code (module_state.spl, convert_nodes.spl,
   parser.spl, ast_stmt.spl — all *interpreted* Simple source, run by the
   seed) never executes before the freeze.
2. The literal string "Deprecated syntax for type parameters" (the last
   diagnostic emitted before every freeze) exists **only** in
   `src/compiler_rust/parser/src/parser_types.rs:414` — it is not present
   anywhere under `src/compiler/**/*.spl`. Emitting it requires the seed's
   own **native** Rust parser, which the seed uses to load/lint the ~2,649
   files transitively `use`d by `native_build_main.spl` itself (the compiler
   driver's own source closure) *before* `native_build_main.spl`'s
   interpreted `main()` (which is what would eventually call into
   `parse_and_build_module`/`flat_ast_to_module`, the code under
   investigation) ever runs. `main()`'s only unconditional early behavior
   (`native_build_entry_args()` / `print_help()` gate) never printed either.

So the flat-AST-bridge hang this bug doc originally describes may still be
real, but it is **unreachable** in the current tree — a different, earlier,
purely-native hang blocks the seed before it gets there.

### What the earlier native hang looks like (report-only, not fixed here)

Traced with `strace -f -e trace=openat`: the process is **not deadlocked** —
it keeps issuing `openat()` calls (38k+ observed, growing ~5 per 20s at the
point of stopping) long after stdout output has frozen. Aggregating the
strace log by path shows heavy redundant I/O, not a simple one-shot file
walk:

- `/home/ormastes/.cache/simple/host/x86_64-unknown-linux-gnu/cpu_config.sdn` — **3,881** opens.
- Directory opens for module resolution: `src/compiler` (3,127), `src/compiler/10.frontend` (696),
  `src/compiler/70.backend` (684), plus **279 opens each** for a long list of
  `src/lib/variants/<arch>/<family>` directories (e.g.
  `x86_64_sse2/{nogc_sync_mut,nogc_async_mut_noalloc,nogc_async_mut,nogc_async_immut,gc_async_mut,common}`,
  mirrored for other ISA variants).
- Only 2,205 *unique* paths were opened across 38,169 total `openat()` calls —
  i.e. the same files/dirs are being reopened roughly 17x on average.

`cpu_config.sdn` and the `src/lib/variants/**` scan are owned by the seed's
CPU/SIMD-variant stdlib resolver — native Rust, not `.spl`:
`src/compiler_rust/compiler/src/stdlib_variant.rs`,
`src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`,
`src/compiler_rust/simd/src/host_config.rs`. `stdlib_variant.rs` does define a
`host_cpu_config()` cache (`reset_host_cpu_config_cache_for_tests()` exists),
so the cache is either not being consulted for this call path or is keyed/
scoped such that it misses on every stdlib-variant module resolution — this
was not root-caused further (native Rust debugging; `ptrace` was unavailable
in this sandbox even with `gdb -p`, so no native stack trace could be taken).
For a ~2,205-file closure this blows up into tens of thousands of redundant
syscalls; the process was still making forward progress (not livelocked) when
stopped after ~4 minutes, so this reads as a severe constant-factor
performance bug (missing memoization in variant/CPU-config path resolution)
rather than a hard infinite loop.

### Disposition

- **No fix applied in this pass.** The instrumentation added for the proof
  (`convert_nodes.spl` `g_flat_bridge_cap_seq` / `[OOB-PROOF]` print) was
  **reverted** — it cannot be compile-verified (the build hangs before
  reaching it) and it serves a theory that is disproven for the reproducible
  hang in this tree. The `SIMPLE_TRACE_AST_RESET` infrastructure already on
  `main` (`ast_reset_seq`, the `ast_reset()` trace print, `STALE-BODY-SUSPECT`
  / `OOB-ABOUT-TO-HIT`) was left untouched and remains ready to re-run once
  the earlier native hang is cleared.
- **Follow-up needed (native, out of scope for this .spl-frontend
  investigation):** profile/cache `host_cpu_config()` and the
  `src/lib/variants/**` directory resolution in
  `src/compiler_rust/compiler/src/stdlib_variant.rs` /
  `interpreter_module/path_resolution.rs` so stdlib-variant module resolution
  is O(1) amortized per process instead of re-reading `cpu_config.sdn` and
  re-scanning variant directories per import. Once that native hang is fixed,
  re-run this bug's proof recipe (`SIMPLE_TRACE_AST_RESET=1`, watch for
  `[ast_reset]` / `[flat-bridge]` / `[OOB-PROOF]`-style markers) to determine
  whether the re-entrant-parse arena race is real.
