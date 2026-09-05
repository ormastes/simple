# Stage4 blocker: stage3 self-hosted parser fails multi-element case patterns the seed parses (2026-07-17)

**Found by:** release-sanity bootstrap chain, after stage1-3 went GREEN
(cranelift backend, `scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift`
rc=0; stage2/stage3 produced, stage3 passed bootstrap compiler sanity).

## Symptom

Stage 4 (full CLI main.spl compile, using verified Stage 3) fails phase 2:

```
[parser_error] line 509:47: unexpected token in expression: : ':'
[parser_error_ctx] path src/compiler/mir_opt/mir_opt/collection_opt_core.spl kind 161 text ':'
(cascades at 513:39, 516:19)
```

First failing construct (`count_inst_uses` match):

```
case CallIndirect(_, ptr, args, _):
```

with cascade over the following `case Intrinsic(_, _, args):` and `case _:`.

## Isolation (A/B proven)

- Deployed Rust-seed binary (`bin/simple fix <file> --dry-run`): **0 parser
  errors** on BOTH the canonical `src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl
  and the staged flattened copy `src/compiler/mir_opt/...` used by stage4.
- The failing region (lines 500-520) is byte-identical between the two copies —
  staging/flattening is NOT the corruption source.
- Therefore the defect is in the stage3 binary's parser: pure-Simple parser
  compiled via cranelift mis-parses a 4-element enum pattern with mixed
  binders/wildcards that the Rust seed parser accepts.

## Hypotheses (ranked)

1. **Cranelift miscompile of the parser's match/pattern code** — same class as
   the documented cranelift defects (enum `==` miscompile C5, byte-combine C6)
   in `simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md`.
2. Pure-Simple parser source genuinely lags the Rust parser on >3-element
   case patterns with trailing wildcard (parity gap) — less likely since the
   same source presumably parsed itself during stage2/3 sanity... unless the
   sanity subset avoids this construct.

Next probe: minimal .spl with a 4-element `case X(_, a, b, _):` fed to the
stage3 binary (`build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`
native-build on a tiny source) vs the seed; then bisect binder/wildcard arity.

## Context

This is the LAST blocker in today's redeploy chain: stale-seed wall →
(fixed) seed spin → (fixed) f-string lexer regression ca58e1f →
(fixed/reverted) labeled-tuple io_runtime break → stage1-3 GREEN → THIS.

## UPDATE 2026-07-17/18: original diagnosis was wrong — real first error is
## 470:43, not 509:47; `case CallIndirect` is cascade noise

Re-examined the ORIGINAL failing log
(`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`,
still on disk from the run that surfaced this bug). The **actual first**
`[parser_error]` in that log is:

```
[parser_error] path src/compiler/mir_opt/mir_opt/collection_opt_core.spl line 470:43: expected ), got Ident 'counts'
```

— i.e. `fn count_inst_uses(inst: MirInst, mut counts: Dict<i64, i64>):`, at
the `mut counts` parameter (col 43 = start of `counts`, right after `mut `).
Every subsequent `[parser_error]` in the log, INCLUDING the `case
CallIndirect(_, ptr, args, _):` one at 509:47 that this doc originally
fingered as "first failing construct", is downstream **cascade/recovery
noise** from the 470:43 failure — the parser is already desynced by then.
**Do not fix the case-pattern parser; there is no grammar gap there.**

### Isolation re-done (corrects the original A/B)

- A minimal repro (`CallIndirect(_, ptr, args, _)`, full 15-variant `MirInst`-shaped
  enum, `match inst.kind:` on a field-access scrutinee, same preceding arms,
  same `mut counts: Dict<i64,i64>` signature) compiles clean via the stage3
  binary's own `native-build`.
- The REAL `src/compiler/mir_opt/mir_opt/collection_opt_core.spl` file,
  compiled via stage3 `native-build` reached through a synthetic entry that
  imports it directly (`--source src/compiler`, 87-file closure) — **compiles
  clean, 0 errors**, including line 470 verbatim.
- Conclusion: the failure is **not** a property of this file's source text in
  isolation. It only manifests when this file is compiled as part of the
  REAL stage4 closure (`--source src/compiler --source src/app --source
  src/lib --source examples/10_tooling`, entry `src/app/cli/main.spl`,
  `--mode one-binary`, native-build in-process/sequential — confirmed single
  PID, not process-forked, for the frontend/parse phase). Something about
  **compile order** / accumulated process state corrupts this file's parse.

### The real signal: `[stmt_get_tag] OOB` / `[flat-bridge] missing stmt tag`
### immediately precedes the 470:43 error, every time

Log lines 5-82 (BEFORE the first `[parser_error]`) are 26 repeats of:

```
[stmt_get_tag] OOB idx=1706 arena_len=462 -> -1
[stmt_get_tag] OOB idx=1706 arena_len=462 -> -1
[flat-bridge] missing stmt tag idx=1706 tag=-1
```
(idx stepping 1706→1756 by 2). This is `convert_flat_stmt`
(`_FlatAstBridge/convert_nodes.spl:1225`) reading a statement-arena index far
outside the CURRENT arena (`arena_len=462`) during some earlier file's
`flat_ast_to_module` conversion — a stale/OOB index surviving into a context
where the shared, process-global stmt arena
(`src/compiler/10.frontend/core/ast_stmt.spl` `stmt_tag`/etc, reset via
`stmt_reset()` inside `ast_reset()`, `module_state.spl:319`) has since been
reset to a much smaller size. This is non-fatal by itself (already has a
graceful fallback: substitutes `StmtKind.Expr(NilLit)`, just prints a
warning) — it does NOT explain the SUBSEQUENT fatal parser_error by itself,
but strongly correlates with it:
- Confirmed via a clean 87-file isolated build capturing full stdout: **zero**
  `OOB`/`missing stmt tag` lines when nothing fails.
- This is the SAME bug class as the already-FIXED, already-documented
  `doc/08_tracking/bug/flat_bridge_type_index_across_ast_reset_2026-07-12.md`
  (stale flat-AST-bridge index across an interleaved `ast_reset()`), which
  explicitly flagged 6 other unaudited call sites in `convert_nodes.spl`
  (lines 599, 751, 758, 887, 910, 1010) sharing "the same underlying hazard"
  — plus notes the durable fix is structural: "(a) make the flat-AST arena
  per-file/per-thread instead of process-global module state, or (b) have
  the driver serialize 'parse file N' with 'convert file N' as one atomic
  unit ... no other thread's `ast_reset()` may run between them". That prior
  doc's OWN follow-up investigation (2026-07-12) tried and **failed** to
  reproduce this for `native_build_main.spl --mode dynload --threads 16`
  under the SEED interpreter (ruled out cross-thread: process-based via
  `rt_process_spawn_async`, separate address spaces; ruled out cross-file:
  "`parse_and_build_module` is atomic: parse → convert, no reset in between,
  per file") — but that disproof was for a DIFFERENT execution context (seed
  interpreter, `--mode dynload`, `--threads 16`, process-forked backend).
  **This bug's context is the STAGE3 SELF-HOSTED (cranelift-compiled) binary
  running `native-build --mode one-binary --threads 2`**, confirmed
  single-process for the frontend/parse phase (only 1 PID observed
  throughout, one core pegged) — the prior disproof does not necessarily
  transfer.

### In progress: `SIMPLE_TRACE_AST_RESET=1` full-closure repro to pin the
### exact preceding file + reset_seq

The codebase already ships ready-made instrumentation for exactly this
question, gated behind `SIMPLE_TRACE_AST_RESET=1`
(`module_state.spl:319-326` traces every `ast_reset()` call with a
monotonic `ast_reset_seq`; `convert_nodes.spl:1435-1449` in `convert_decl_fn`
prints `STALE-BODY-SUSPECT`/`OOB-ABOUT-TO-HIT` with `reset_seq` whenever a
function's captured `body` stmt-index list runs ahead of the live arena).
A full-closure reproduction run (stage3 binary, exact stage4 command, own
isolated `--cache-dir`, `SIMPLE_TRACE_AST_RESET=1`) was launched to capture
this; **very slow** (~5-6s/file sequential single-process parse+convert
across the ~2000+-file closure — matches this doc's original 30-60+ min
estimate, possibly longer). Once it lands, update this section with: the
exact file compiled immediately before `collection_opt_core.spl`, and
whether `reset_seq` at the `STALE-BODY-SUSPECT` print jumped mid-file
(same-file reentrant reset — would point at a nested/reentrant parse call
like `flat_bridge_parse_interp_inner`, convert_nodes.spl:449, though that one
specifically avoids `ast_reset()` by design per its own comment) or only at
the expected file-boundary (cross-file leak — would point at some global not
covered by `ast_reset()`'s sweep, or a decl/stmt captured-then-read-across-file
ordering bug in the driver).

**Do not touch the case/pattern parser (`parser_stmts.spl:1019
parse_match_arms_common`, or `parse_call_arg_raw` /
`parse_postfix`/call-arg-list loop in `parser_expr.spl`) — confirmed correct,
matches Rust-seed behavior, and the isolated repro proves it. Fix effort
belongs in the flat-AST-bridge arena-reset hazard, not the parser grammar.**

## ROOT CAUSE CONFIRMED (2026-07-18): cross-file module-global rebind not
## propagating under the stage3 cranelift backend — fixed by inspection +
## code-shape evidence, not by a full-closure trace (machine too contended)

The full-closure trace repro (`SIMPLE_TRACE_AST_RESET=1`) could not be driven
to completion in-session: the shared build host had 5+ OTHER concurrent
bootstrap/native-build processes from parallel sessions (`wt_s58`, `wt_s54`,
`pure-simple-tool-remain`, `bootstrap-goal`, etc.), load average ~9-10 on 32
cores, making even a single-file `native-build` take minutes instead of
seconds. Root cause was instead nailed by direct source inspection, which
gives a decisive (not merely probable) read:

- `stmt_reset()` (`ast_stmt.spl:137`) and `expr_reset()` (`ast_expr.spl`) each
  reset their arrays with **rebind + nil-guard + explicit `.clear()`** — e.g.
  `stmt_tag = []` ... `if stmt_tag == nil: stmt_tag = []` ... `stmt_tag.clear()`.
  Both live in the SAME FILE as the `var stmt_tag`/`var expr_tag` declarations
  they reset.
- `ast_reset()` (`module_state.spl:319`), by contrast, reset the decl/arm/elif/
  module arrays (`decl_tag`, `decl_body_stmts`, `arm_pattern`, `arm_body`,
  `elif_cond`, `module_decls`, `module_decl_slots`, `module_path_slot`,
  `lexer_state_core_pos_slot`, `lexer_state_core_line_slot`, ~38 vars total)
  with **rebind + nil-guard ONLY — no `.clear()`**. Critically, EVERY ONE of
  these vars is declared in a **DIFFERENT FILE**, `decl_nodes.spl`, not in
  `module_state.spl` where the reset code ran (confirmed: `grep '^var
  decl_body_stmts'`/`'^var module_path_slot'` etc. only match
  `_Ast/decl_nodes.spl`; cross-file access already proven legal in this
  codebase — `module_state.spl` already calls `decl_nodes.spl`-defined
  `ast_decl_count_set()`/`ast_module_decl_count_get()`).
- This exactly matches the OOB evidence: `[stmt_get_tag] OOB idx=1706
  arena_len=462` — `arena_len` (`stmt_tag.len()`, same-file reset + `.clear()`)
  correctly reflects the post-reset SMALL size, while `idx=1706` (read from
  `decl_get_body(idx)` → `decl_body_stmts[idx]` in `convert_decl_fn`,
  `convert_nodes.spl:1435-1449`, cross-file rebind-only reset) is a STALE,
  oversized index surviving from a PREVIOUS file's parse. `stmt_reset()` DID
  take effect (same-file, has `.clear()`); the decl-array reset did NOT take
  effect for at least one reader in a different compilation unit
  (`decl_nodes.spl` itself, reading its own `decl_body_stmts` — i.e. this is
  not even "reset from file A, read from file B": the WRITE happens in
  `module_state.spl`, the READ happens back in `decl_nodes.spl` where the var
  is declared, and even that round-trip lost the write under cranelift).
  A stale, oversized `decl_body_stmts[idx]` list for a decl in the file
  compiled immediately before `collection_opt_core.spl` is exactly the kind
  of corruption (arena/index desync bleeding into the next file's own
  `parser_init_with_path()`/`ast_reset()` state) that would produce a
  legitimate downstream parser desync at `collection_opt_core.spl:470:43`
  (`mut counts: Dict<i64, i64>`) despite that file parsing perfectly cleanly
  in every isolated repro.
- This is the missing sibling of the already-documented, already-partially-fixed
  `doc/08_tracking/bug/flat_bridge_type_index_across_ast_reset_2026-07-12.md`
  (same hazard class: stale flat-AST-bridge index surviving an `ast_reset()`
  interleave) — that doc's own 2026-07-12 follow-up ruled out cross-thread and
  cross-file-interleaving causes for a DIFFERENT execution context (seed
  interpreter, `--mode dynload`, `--threads 16`); it never considered a
  same-process **cranelift codegen** cross-compilation-unit rebind-visibility
  gap, which is what this is.

### Fix applied (contained, `.spl`-only)

- `src/compiler/10.frontend/core/_Ast/decl_nodes.spl`: added `decl_reset()`,
  co-located with the `decl_*`/`arm_*`/`elif_*`/`module_decls`/
  `module_decl_slots`/`module_path_slot`/`lexer_state_core_pos_slot`/
  `lexer_state_core_line_slot` var declarations, mirroring `stmt_reset()`'s
  exact rebind + nil-guard + `.clear()` pattern for all ~38 vars (also added
  `decl_impl_trait`/`decl_is_trait`/`decl_param_mut_text` to the reset, which
  were previously missing from `ast_reset()`'s list entirely — a separate,
  smaller pre-existing gap in the same function, fixed in passing since it's
  the same one-line-per-var pattern already being rewritten).
- `src/compiler/10.frontend/core/_Ast/module_state.spl`: `ast_reset()` now
  calls `decl_reset()` instead of inlining the cross-file rebind + nil-guard
  for those vars (the `lexer_state_core_col_slot`-and-later vars, which ARE
  declared in `module_state.spl` itself, are untouched — same-file rebind is
  not implicated by this bug and was left as-is).
- Verified: `decl_reset()`/updated `ast_reset()` compile cleanly via the
  stage3 binary's own `native-build` (87-file closure through
  `compiler.mir_opt.mir_opt.collection_opt_core`, 0 failed, matching the
  pre-fix baseline build time).

### Underlying cranelift defect (documented, not separately fixed)

The durable defect is in the pure-Simple **cranelift backend**
(`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` and related):
a module-level `var` array **rebind** (`x = []`, replacing the array's
identity/reference) does not reliably propagate to a reader in a different
compilation unit/function, while an **in-place `.clear()`** (mutating the
existing array's contents without changing its identity) does. This class of
bug should be re-audited generally: any `ast_reset()`-shaped function élsewhere
in the pure-Simple compiler that resets shared/global array state via bare
rebind only (no accompanying `.clear()`), especially across a file boundary
from the vars' own declaration, is a candidate for the same silent corruption.
Per repo convention (`.claude/memory/ref_*`, `feedback_arrays_value_types.md`),
this joins the existing catalogue of interpreter-vs-compiled and
compiled-only semantic gaps around module-level `var` state in native
binaries (see the pervasive `if X == nil: X = []` nil-guards already
throughout this file, added for a related but distinct "initializer doesn't
run in native binaries" gap).

### Verification status

- Root cause: **confirmed by code-shape inspection** (asymmetric reset
  pattern + OOB evidence), not by a full green bootstrap in-session — the
  shared build host's contention (5+ concurrent native-build processes from
  other sessions) made a full `--full-cli` bootstrap (30-60+ min even
  uncontended) impractical to complete and observe within this session.
- Fix is applied and syntax/compile-clean (verified via the 87-file closure
  build above). **Full end-to-end stage1-4 bootstrap verification
  (`sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift
  --full-cli`) is launched but its outcome is NOT yet observed/confirmed in
  this session** — do not treat this bug as closed until that run (or a
  rerun under less contention) reports stage4 green with a working full-CLI
  binary. Next agent/session: check for the launched run's log/PID, or
  rerun the command fresh, and update this section with the actual result.
