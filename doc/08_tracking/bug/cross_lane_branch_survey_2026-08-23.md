# Cross-lane branch survey — what to adopt from six sibling branches (2026-08-23)

Status: SURVEY COMPLETE. **Nothing ported as code.** Two hard stops and one
anti-pattern recorded below. Read this before anyone merges these branches.

Base surveyed: `origin/main` at `ee1431e8138` .. `ee40943016a` (moved twice
during the survey).

## Verdict per branch

| ahead | branch | verdict |
|---|---|---|
| 130 | `codex/compiler-performance-memory-audit-20260823-v21` | **HARD STOP — do not merge.** Cherry-pick only, and only after bootstrap phase 4. |
| 26 | `codex/session-01a023a8-sync14` | **Fully duplicated on main.** Nothing to port. |
| 6 | `codex/stage3-hir-owner-fixes` | Not surveyed — owned by another lane (macOS). |
| 1 | `codex/metal-i64-abi-gc-env-import` | Darwin + a **workaround for a bug we already fixed properly**. Do not port. |
| 1 | `codex/x86-bootstrap-readiness-sync1` | Duplicate of a fix already on main. |
| 1 | `codex/x86-bootstrap-readiness-sync2` | Doc + spec only for the same already-landed fix. |

## HARD STOP 1 — the 130-commit perf branch guts the MIR optimizer

Merge-base `4af0d34a813`; `main` is **179 commits ahead of that base**. A naive
merge therefore rewinds a great deal.

The branch contains a ~15-commit cluster (`harden:` / `fix(optimizer): quarantine …`)
that replaces whole optimizer passes with fail-closed **skeletons**:

- `93edc2063c4` DCE — `dce.spl` 418 lines -> 19 (-399)
- `cc6cfb9a109` GVN — `gvn.spl` -360
- `29414ba09a4` TCO — `tco.spl` -139
- plus `8beeb2f35c0` constant folding, `1d9d90d1be6` copy propagation,
  `0aa96b90e3e` local CSE, `5d5250a500c` body outlining,
  `5e3e95dc088` generator state machine, `1f0b687a413` general loop transforms,
  `ad07851186d` bounds-check elimination, `f918cdcba78` strength reduction,
  `53a41c10a6e` string-builder rewrite, `dde43e93de6` trip-count recognizer,
  `d03bbeb8155` hoist bodies, `529b450c637` collection loop hoisting.

`dce.spl` header on that branch: *"DCE is inactive until every MIR opcode has
complete DEF/USE, observability, trap, ownership/destruction, unwind,
volatile/atomic/device, and debug-probe semantics."*

That may be a defensible correctness position, but it is a **whole-compiler
codegen behaviour change**, taken unilaterally on a branch 179 commits behind,
and it collides with `main`'s own landed work in the exact same files
(`1e6f5216e8e` MIR backend fail-open -> assert touched `dce.spl`, `gvn.spl`,
`tco.spl`, `cse.spl`, `copy_prop.spl`, `outline.spl`, `generator_sm.spl`,
`loop_strength.spl`, `string_builder_opt.spl`, `collection_opt_patterns.spl`).
Merging it naively would silently revert that. **Requires an explicit,
owner-level decision, not a sync.**

## The rest of the 130 commits, clustered

- **~60 commits `perf(lint)` / `perf(cli)` / `perf(fix)` / `perf(vhdl)`** —
  developer tooling hot paths (lint rule registries, diagnostic JSON scanning,
  easyfix rewriting, VHDL catalog sorting). Real work, but *not* the bootstrap
  compiler hot path, so near-zero value against the current RSS goal.
- **~10 commits `feat(mir-opt)` verifier receipts / SSA dominance / ABI local
  verification** — plausible correctness value, but sits on top of the
  quarantine cluster and cannot be lifted independently.
- **~7 commits, the only cluster with real bootstrap-perf value:**
  `a2ea74d3342` scope silent trace output (adds `10.frontend/trace_policy.spl`),
  `14875186a65` cache compiler trace per parse, `e8a48dbfd76` scope flat-bridge
  trace policy, `5a2e6c3fd8e` share parse profiling policy,
  `cc013115ded` scope MIR lowering trace policy, `bd3b29b00fd` snapshot LLVM
  adapter operation policy, `dda5356ea20` group MIR storage overlap analysis.
  These avoid building trace/policy state on every parse and lowering step —
  the same defect *class* as the COW-alias record
  (`value_semantics_cow_alias_perf_class_2026-08-21.md`).

  **Measured cherry-pick trial of the chain head `a2ea74d3342` onto `main`:**
  12 frontend files applied cleanly; one content conflict
  (`src/app/cli/query_lint.spl`) plus 5 modify/delete conflicts on
  branch-local `.spipe`/`doc` files. So it is *portable*, at the cost of a
  4-commit ordered chain touching `parser.spl`, `parser_stmts.spl`,
  `parser_expr.spl`, `ast_stmt.spl`, `_AstExpr/nodes.spl` and the flat-AST
  bridge.

  **Deliberately NOT ported now, and this is the reason:** a phase-2 bootstrap
  is LIVE against `main` as of this writing. Rewriting the parser and MIR
  lowering hot path under a running multi-hour bootstrap, with no local
  before/after measurement to justify it, trades a known-good build for an
  unquantified win. Revisit after phase 4 admits, port the chain in order, and
  gate it on an A/B parse-phase measurement in its own `SIMPLE_CACHE_SCOPE`.

## HARD STOP 2 — the metal branch normalizes a workaround for a bug main fixed

`3bba453bfc3` adds `gc_env_get` to `src/lib/gc_async_mut/io/env_ops.spl` with the
comment *"Stable uniquely-named owner for older bootstrap compilers whose native
codegen cannot preserve a renamed function import at the call site"*, and rewrites
`use … {env_get as gc_env_get}` into a plain import to dodge it.

`main` landed the **real** fix for that defect today: `aac03e9d65a`
(interpreter aliased imports). Porting the workaround would violate CLAUDE.md's
rule against silently normalizing a workaround, and would leave a permanent
alias-avoidance pattern in the stdlib. The branch's existence is nonetheless
useful corroboration that renamed-import loss was a real, independently
observed defect class.

The rest of that commit (`metal_sffi` i64 ABI, `metal_graphics_runtime.rs`) is
macOS-only. `rt_cstring_to_text` in `runtime_native.c` is arch-neutral and small
but has no Linux consumer.

## Duplicates already on main — verified, not assumed

- `fa142fe4687` / `56cfe9e3a0a` / `8e088e40ddf` "remove orphan signature
  projection remnants": `grep -rn 'imported_surface_projected_name_type\|module_surface_signature_index' src/`
  on `main` returns **zero hits**. Already gone.
- `47a67cca93d` / `27589ead96a` raw-ABI snapshot fixes: `main`'s
  `driver_mem_snapshot.spl:41-45,71` and `driver_log_helpers.spl:51-58` already
  lower every `text` through `rt_string_data`/`rt_string_len`. Already fixed.
- `stage3_current_source_hir_rss_termination_2026-08-14.md`: `main`'s copy is
  43,369 bytes and is a strict **superset** — the sync14 version is 18 lines
  shorter. Nothing to merge back.

## The one genuinely valuable finding, already on main

For anyone chasing the ~3.1 GB worker RSS: the evidence in
`stage3_current_source_hir_rss_termination_2026-08-14.md` is the sharpest lead.
Live backtrace at termination was in `rt_transient_raw_insert` via `rt_alloc`,
under a repeating chain of `register_imported_symbol_inner`,
`materialize_imported_field_dependency_inner`, `register_imported_type_methods_inner`.
Module 1 RSS went 640,620 KiB -> 3,664,420 KiB -> 8,135,496 KiB in ~44s.

The sync14 lane also recorded a **negative result worth not repeating**: an
exact-registration-tuple in-flight guard was implemented, measured, and
*disproved* as the fix (module 0 unchanged, module 1 still blew up), then
reverted (`04aaa65475f` -> `da82678637e`, with `5eeb1091baa` documenting the
rejection). So the fan-out is repeated acyclic expansion, or a cycle whose key
changes per hop — not an exact tuple cycle. Next step is measuring distinct
registration-key cardinality and key-length growth during module 1.

## Things NOT adopted from the check-script clusters

`sync14` and the perf branch both modify pre-push guards
(`check-tree-size-push.shs`, `check-push-must-pass.shs`, `check-rules-sdl.shs`;
perf-branch `23f6880bd8c` "bound push tree inspection to tip",
`5cf3be7c02a` "bound multi-ref evidence validation"). Some are plausibly
legitimate speedups, but every one of them narrows what a guard inspects, and
this repo's history has four tree wipes that a narrowed guard is exactly how you
miss. Not adopted here; if wanted, each needs its own commit with a neuter proof.

## Method note

Survey done read-only from a private detached worktree
(`/mnt/data/worktrees/othersync-1`). No sibling lane's worktree, process or
branch ref was touched. The single cherry-pick trial was `-n`, aborted, and the
worktree hard-reset to `origin/main` before any commit.
