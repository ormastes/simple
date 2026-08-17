# Stage4 dies in phase 3 on a flat-AST statement-arena desync, masking the unresolved-type layer

- **Date:** 2026-08-01
- **Status:** **STILL OPEN** — root cause (why a stale index reaches an
  accessor at all) unresolved. The *containment* half is now closed for the
  statement family; see "Triage 2026-08-17" at the bottom.
- **Owner:** `codex-stage4-bootstrap-close` (claimed 2026-08-02)
- **Severity:** HIGH — this is the blocker standing in FRONT of the
  `unresolved type` layer. Three lanes are chasing symbols that a stage4 build
  cannot currently reach.
- **Area:** `src/compiler/10.frontend/` flat-AST bridge / statement arena
- **Tip measured:** `ecf13e1cf3f8ed7636cf63beecd0e88895e4a7db` (tree 109,555 files)

## What was measured

A real stage4 build — the only path that runs the passes emitting
`unresolved type` / `unresolved name` (see
`stage3_clean_baseline_is_bootstrap_flat_artifact_2026-08-01.md`) — was run with
the exact env and flags of `bootstrap_native_build_main`
(`scripts/bootstrap/bootstrap-from-scratch.sh:590`): `SIMPLE_BOOTSTRAP_STAGE4=1`,
`--mode one-binary`, `--entry src/app/cli/main.spl`, `--entry-closure`,
`--low-memory`, four `--source` roots, llvm backend.

Parent compiler: a stage2 built from the same tip by the frozen Rust seed
authority (`stage2 exit=0`, 4m17s).

Result:

| Metric | Value |
|---|---|
| stage4 exit | **1** |
| wall clock | 24:46 |
| user CPU | 1477.89 s |
| peak RSS | 1,442,152 KB (1.44 GB) |
| distinct `.spl` paths in log | 1,213 |
| `[hir-lower]` lines | 555 |
| `unresolved type` occurrences | **0** |
| `unresolved name` occurrences | **0** |
| `unresolved import` occurrences | **0** |

All counts taken with `/usr/bin/grep` (GNU), not the ambient ugrep.

## The failure

```
[stmt_get_tag] OOB idx=13 arena_len=5 arena_gen=591 -> -1
[flat-bridge] missing stmt tag idx=13 tag=-1
...
[ERROR] phase 3 FAILED
```

- 6,474 `[stmt_get_tag] OOB` events.
- The FIRST one is on log line 1 — the desync is present from the very first
  module, not after some deep traversal.
- Many carry `arena_len=0`: the statement arena is EMPTY while the flat-AST
  bridge is still asking it for statement tags. Observed generations include
  `arena_gen=` 591, 1053, 1077, 1329, 1495, 2117, 2409, with `arena_len` 0, 5,
  and 156 — i.e. the arena is being reset/rotated underneath readers that still
  hold indices from a previous generation.
- `bootstrap-from-scratch.sh:1617` already treats exactly this signature
  (`\[stmt_get_tag\] OOB|\[flat-bridge\] missing (stmt|expr) tag`) as a hard
  Stage 4 failure, so this is a known-fatal class, not noise.

## Why this matters for the unresolved-type lanes

`phase 3` IS HIR lowering — the phase that emits `unresolved type`. It **failed**.
So the zero counts above are **not** evidence that `HirType`, `MirSignature`,
`MirAsmOperand` or `HirBlock` now resolve. They are evidence that HIR lowering
aborted before the tree was covered. This is the same category of invalid
inference the stage3 bug doc retired, one layer up:

> a build that stops early reports no diagnostics from the passes it never
> completed.

**Consequence:** the `HirType` +258 / `MirSignature` +121 / `MirAsmOperand` +106
/ `HirBlock` +104 census can be neither confirmed nor retired until the arena
desync is fixed. Any lane told "your targets are closed" on a stage4 run that
exited 1 in phase 3 has been given the same artifact in new clothing.

## Ordering

Fix the statement-arena generation/reset discipline first. Only a stage4 run
that reaches the END of phase 3 produces a census that can retire or confirm the
unresolved-type layer.

## Reproduction

Stage2 from the tip, then `bootstrap_native_build_main <stage2> <out>` verbatim.
Build in tmpfs; `/dev/shm` works, `/run/user/1000` is wiped on session restart
(it destroyed one full run during this investigation).

## Adjacent, already settled (do not re-derive)

- `bootstrap_closure` = `SIMPLE_BOOTSTRAP=="1" and
  SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=="1"`, read via `hir_module_env_get`
  (`20.hir/hir_lowering/_Items/module_lowering.spl:1222`). On the stage3/stage4
  entry path `bootstrap_main.spl` seeds it to `"0"` and
  `driver_source_pipeline_loading.spl:252` flips it to `"1"` **unconditionally**
  after the closure walk. It is therefore 1 during HIR lowering; "closure never
  enabled" is NOT a live mechanism.
- `export use M.*` records NO item list, so the facade's `Module.exports` stays
  empty (`10.frontend/core/parser_decls_use.spl:205`) and the re-export was
  visible only through the `facade_shape` gate in
  `register_glob_imported_symbols_depth`. Commit `3226faaf9eb` ungated that
  recursion behind a per-root memo, which closes this route.

---

## Triage 2026-08-17 — root cause STILL OPEN; the crash mechanism is contained

**Binary used, stated explicitly:** `bin/simple` ->
`bin/release/x86_64-unknown-linux-gnu/simple`, the **Rust seed** (59,536,728
bytes, mtime 2026-08-16 22:59). No self-hosted stage2/stage3 binary exists in
this checkout and `build/bootstrap/**` was off-limits (a live bootstrap owned
by another lane), so **the stage4 build in "Reproduction" above was NOT re-run.**
Nothing below claims otherwise, and the row is NOT closed.

### What WAS reproduced, cheaply and without a bootstrap

The doc's own failure signature is reachable from a plain `bin/simple run`
probe over the arena API — no stage4, seconds not minutes:

```
$ bin/simple run probe.spl      # stmt_alloc; ast_reset(); stmt_reset(); read the held index
TAG
[stmt_get_tag] OOB idx=12 arena_len=0 arena_gen=1 -> -1
-1
SPAN
error: semantic: array index out of bounds: index is 12 but length is 0
rc=1
```

That is the doc's `[stmt_get_tag] OOB idx=… arena_len=0 arena_gen=…` line
verbatim in shape, followed by the **process abort** — the "index is 48 but
length is 13" class named in `_AstExpr/accessors.spl`.

### The mechanism the log flood was hiding

`stmt_get_tag` was guarded and correctly returned its `-1` sentinel. Its five
siblings — `stmt_get_span`, `stmt_get_expr`, `stmt_get_name`, `stmt_get_type`,
`stmt_get_body` — indexed their backing arrays with **no bounds band at all**.
So a walker did exactly what it was supposed to do (read the tag, get -1, take
the default branch) and then died on the next field read of the same stale
statement. `stmt_get_gpu_grid`/`stmt_get_gpu_block` banded only the UPPER end,
so `-1` itself passed their `idx < len` test and indexed negatively.

This asymmetry was already written down and then not acted on: the comment
block in `src/compiler/10.frontend/core/_AstExpr/accessors.spl` closes exactly
this family for EXPRESSIONS and says *"The statement half of this family is the
measured reproducer"* — i.e. the half known to be the reproducer is the half
that was left unguarded.

### Fix applied (containment only)

`src/compiler/10.frontend/core/ast_stmt.spl`: added `stmt_idx_is_live` +
`stmt_oob_trace` and banded all five sibling accessors, plus both ends on the
two GPU accessors. Mirrors the expression half exactly, including its knob
(`SIMPLE_TRACE_AST_OOB`, default off, so one stale subtree cannot flood the log
with a line per field read) and its neutral-sentinel convention (-1 / "" / []).
The env-mirror read stays FIRST, as in `stmt_get_tag`: under
`SIMPLE_BOOTSTRAP=1` module-var arrays do not persist and the mirror is the only
live store, so banding ahead of it would reject live indices.

### Evidence

| | `Results:` line |
|---|---|
| before (ablation: guards removed via `git stash`) | `Results: 7 total, 2 passed, 5 failed` |
| after | `Results: 7 total, 7 passed, 0 failed` |

Ablation ran the fix in, out, and back in — causation, not correlation. Specs
(`bin/simple test --no-session-daemon`, tree-walk interpreter):

- `test/01_unit/compiler/frontend/stmt_accessor_stale_index_guard_spec.spl` —
  reproducer. `Results: 7 total, 7 passed, 0 failed`.
- `test/01_unit/compiler/frontend/ast_arena_accessor_family_fail_closed_spec.spl`
  — CLASS detection: sweeps the whole accessor family with both non-live index
  shapes (past-the-end AND negative), so the next unguarded sibling is caught by
  an existing test rather than by a stage-4 crash log.
  `Results: 4 total, 4 passed, 0 failed`.

### Why the row stays OPEN

Containment turns a process abort into a `-1`. It does **not** answer the
question this row is actually about: **why does a reader hold a statement index
across an `ast_reset()`?** The generation machinery in
`core/_Ast/module_state.spl` (bump-before-clear, `_ast_harden_retire_snapshot`)
and the symmetric env-mirror clears on both the stmt and expr sides are all
present in current source and are all *diagnostic or hygiene* measures — none
of them prevents the interleaved reset. Note also that the L6 promise in
`ast_stmt.spl` ("diagnosable from ONE line instead of an OOB flood") is **not**
implemented for statements: `ast_gen_check_index` is called from the expression
accessors only, and the statement arena records no minted-generation per index
to pass it. That is why the failing run logged 6,474 OOB events rather than one
stale-generation line. Both remain open work, and the ordering claim in
"Ordering" above still stands: only a stage4 run that reaches the END of phase 3
can retire or confirm the unresolved-type census.
