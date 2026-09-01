# Stale-snapshot clobber: `4edef8fab8e` ("feat: snapshot current development state")

Status: **PARTIALLY REPAIRED — NOT fully accounted for.**
Filed 2026-08-26. Audit + first repairs 2026-08-27.

## What happened

`4edef8fab8e` (single parent `993760b729f`, author `t`, 2026-08-26 01:21 UTC)
landed a whole-tree snapshot captured from a **stale** working copy. It rewound
files that other sessions had already moved forward, and deleted files that code
still in the tree continues to reference.

## Corrected scale — the original ticket numbers were wrong

The first write-up said "624 files, -45k lines, 2 spec files truncated". Measured
directly from git, the real shape is roughly **18x larger**:

| measure | ticket claimed | actually measured |
|---|---|---|
| files touched | 624 | **11,225** |
| lines added | — | 1,275,284 |
| lines deleted | 45,000 | **860,823** |
| files fully deleted | — | **544** |
| files with net line loss | — | **6,505** |
| spec files truncated to 1 byte | 2 | **7** |
| tree file count | — | 120,170 -> 119,850 (-320) |

Anyone re-deriving these: the columns of `git diff --numstat` are
`added <TAB> deleted <TAB> path`. Summing `$2`/`$3` instead of `$1`/`$2` yields
the nonsense "+860823 / -0" and will send you down the wrong path.

## Current damage in `origin/main` (baseline `2b35049f8d7`)

Two disjoint populations. Both were measured by blob-id comparison, not by
reading diffs:

1. **Still absent** — deleted by the clobber and never restored: **523** of the
   544 (9 restored by earlier sessions and 12 restored in Batch 3 below).
   `doc` 307, `test` 155, `src` 50, `scripts` 9, `.spipe` 1, `examples` 1.
2. **Still rewound** — file still present but today's blob is byte-identical to
   the clobber's blob and differs from the pre-clobber blob, i.e. nothing
   forward ever touched it and it still carries the rewound content: **5,801**
   paths. `test` 5,173, `src` 324, `doc` 268, `scripts` 17, `.claude` 7,
   `examples` 4, `.codex` 2, `tools` 1, `.spipe` 1, `README.md` 1.
   Net lines lost in `src/` alone: **14,838**.

Of the 324 rewound `src/` files, **129 are strict supersets** (the clobber
deleted lines and added none, so restoring the pre-clobber blob is purely
additive and safe) and **195 are not** — those need a real hand-merge, because
origin/main carries lines the pre-clobber version never had. Re-running the same
superset test across the 195 found only **1** extra safe file, so **194 files
genuinely require hand-merge**.

## What was repaired

### Batch 1 — 7 truncated unit specs (landed)
Truncated from ~3 KB to 1 byte. Pre-clobber blob verified byte-identical to
`26de1a115c3`, so no generation ambiguity. All 7 pass: 42 assertions, 0 failures.

```
test/unit/compiler/frontend/lexer_types_spec.spl
test/unit/compiler/frontend/ast_types_spec.spl
test/unit/compiler/common/{config,error_types,effects,di,gc_config}_spec.spl
```

### Batch 2 — 105 pure-rewind `src/` files (landed)
The 129 strict-superset files minus 24 held back as entangled (below). +879 lines.

Verified:
- `cargo check --release --bin simple` — clean.
- `sh scripts/check/check-c-runtime-compiles-push.shs` —
  `PASS — 118 file(s) compiled, 0 errors`.
- The 7 Batch-1 specs — all `rc=0`, 6/6 assertions each.
- `bin/simple test test/unit/compiler` — **does NOT reach a verdict**, with or
  without this change. It aborts at `exit=1` with
  `error: semantic: variable mcdc_dynamic_probe_controller_load_builtin_current_owner not found`
  and never prints a `Results:` line. Confirmed **pre-existing on clean
  `origin/main`** by re-running it against a stashed tree: byte-identical
  failure and exit code. So this batch introduces no new failure there, but the
  suite is *not* evidence of a pass — it is a pre-existing red that should be
  filed separately. An earlier draft of this record claimed "no new failures"
  on the strength of a `grep` that matched zero lines; that was a vacuous check
  and has been corrected.

On the PR's `-67` deleted lines: none of it comes from the 105 restored `src/`
files. Checked per file with
`git diff origin/main -- <f> | grep '^-' | grep -v '^---'` across all 105 — the
result is **zero deleted lines in every one of them**. The restores are strictly
additive, as the superset test predicted. The `-67` is accounted for by the 7
truncated specs (whose 1-byte content is replaced) and by this record itself
being rewritten.

### Batch 3 — 5 dangling-export sources, 1 transitive source, and 6 specs

After rebasing this PR onto `origin/main` at `eccb04c8018e`, a complete audit
of the 112 Batch-1/Batch-2 paths found five restored public facades that named
modules still deleted by the clobber. Each missing source has an exact blob in
the immediate pre-clobber parent `993760b729f`. The restored scheduler registry
then exposed one transitive import of the still-deleted `server_launch_grants`.
All six sources were restored byte-for-byte, together with every matching spec
that was still absent:

```
src/compiler/00.common/dependency/member_visibility.spl
src/compiler/35.semantics/lint/cow_alias_hotpath.spl
src/compiler/70.backend/backend/common/mir_inst_variant_name.spl
src/compiler/90.tools/lint/_LintMain/nonexistent_type_lints.spl
src/os/kernel/loader/server_launch_grants.spl
src/os/kernel/scheduler/server_data_launch_grant_registry.spl
test/01_unit/compiler/dependency/member_visibility_spec.spl
test/01_unit/compiler/hir/member_visibility_enforcement_spec.spl
test/01_unit/compiler/lint/cow_alias_hotpath_product_fixes_spec.spl
test/01_unit/compiler/lint/cow_alias_hotpath_spec.spl
test/01_unit/compiler/lint_nonexistent_type_rules_spec.spl
test/01_unit/os/kernel/loader/server_launch_grants_spec.spl
```

The scheduler registry's matching spec was already present on `origin/main`
and byte-identical to the pre-clobber blob. No dedicated MIR variant-name spec
existed in the pre-clobber tree, so none was invented. The resolver-backed
dangling-import gate resolved the facade/source pairs and the transitive loader
dependency with zero dangling edges (12 files checked; one timed out and
remains explicitly unverified).
Executable compiler/spec verification remains blocked by the available
self-hosted binaries: the current artifact is a forbidden Rust seed, the older
pure-Simple artifact crashes with exit 139 on the compiler tree and all seven
focused specs, and the newer stage artifact does not implement `check`.

### Batch 4 — spawn recipe semantic cluster

After a conflict-free rebase onto `origin/main` at `15fef1d8e406`, the
production recipe owner and its coupled evidence were restored exactly from
the immediate pre-clobber parent:

```
7424484f1bfd  src/os/kernel/loader/spawn_recipes.spl
ce517332c301  test/01_unit/os/kernel/loader/spawn_seal_readiness_spec.spl
3bdfac8cb91a  src/os/kernel/loader/arm64_authenticated_media_fixture.spl
b670ce4695dd  src/os/kernel/loader/riscv64_authenticated_media_fixture.spl
ae118465e0b6  src/os/kernel/loader/x86_64_authenticated_media_fixture.spl
```

This restores the authenticated-server and SSH recipes,
`spawn_recipe_launch_contract_valid`, and the six Clang compile/link/execute
recipe constants used by production and specs. The matching
`clang_spawn_recipes_spec.spl` already had its pre-clobber blob and was not
rewritten. All imported named symbols were present in their current owners.
The resolver-backed closure included 18 production consumers, specs, and import
owners and reported zero module or symbol dangling edges; one file timed out and
remains explicitly unverified. This was verify/fix cycle 3, so the closure was
not rerun and no further cluster expansion was attempted.

## Entanglement found — restores are NOT independent

Restoring a rewound file frequently drags in a *still-absent* companion. This is
positive evidence the deletions were clobbers, not deliberate removals. Three
clusters were isolated and **deferred**:

- **Rust seed (18 files).** Restoring `common/src/lib.rs` gives
  `E0583: file not found for module engine_receipt` — `engine_receipt.rs` is in
  the still-absent set. Restoring that too then yields 7 more errors:
  `E0432 unresolved import simple_runtime::value::rt_heap_ref_wellformed` and
  `E0425` for `perf_counters::{STEAL_OK, STEAL_MISSING, STEAL_MISMATCH,
  STEAL_INNER_SHARED, STEAL_OUTER_SHARED}`. Those definitions live in
  hand-merge-only files. The Rust half cannot be restored piecemeal.
- **test_runner (5 files + `src/lib/nogc_sync_mut/spec/in_development.spl`).**
  `test_runner_args.spl` / `test_runner_single.spl` set `TestOptions.whole`, but
  the `whole` field — along with `TestOmissionStatus`, `TestOmissionEvidence`,
  `BlockedScenario`, `UnsupportedScenario` — was stripped from
  `test_runner_types.spl`, which is a hand-merge file. Restoring the cluster
  without it breaks every spec with
  `Cannot infer field type: struct 'TestOptions' field 'whole'`.
  Separately, `test_runner/__init__.spl` needs `spec/in_development.spl`
  (still absent) or every spec dies with
  `Module "std.spec" does not export 'in_development'`.
- **`src/runtime/test/rt_transient_heap_scope_selfcheck.c`.** Calls
  `rt_transient_scope_promoted_nodes`, still undeclared; restoring it turns the
  C runtime gate RED.

## NOT part of this incident

20 zero-byte `.spl` files in the tree (`src/compiler/99.loader/*`,
`src/compiler/test_pkg/mod.spl`, `src/app/debug/remote/types.spl`, the
`python_inspired_sample/` fixtures) were **already 0 bytes before the clobber**
— verified at both `4edef8fab8e~1` and `26de1a115c3`. They are pre-existing
placeholders. Do not "restore" them.

## Still open

- **523 still-absent files** — `engine_receipt.rs` and
  `spec/in_development.spl` were examined individually; both proved to be **real
  clobbers**, each surfaced by a build/test break rather than by inspection. The
  12 Batch-3 paths are also confirmed clobber deletions because their surviving
  public facades or transitive imports still require them. The other 521 are
  unclassified.

  **No deletion in this incident has been confirmed deliberate.** The
  deliberate-vs-clobber split the original ticket asked for therefore stands at:
  544 deleted, 21 restored, 14 proven clobbers, **0 confirmed deliberate**, 521
  unclassified. Every piece of evidence gathered so far points the same way —
  that this was an undifferentiated stale snapshot, not a set of intentional
  removals — but that is an inference from the examined paths, not a
  finding. Do not record a deliberate count without per-path evidence. The `doc` (307) and `test` (161) majorities are
  probably bulk-restorable, but were not attempted.
- **5,801 still-rewound files**, of which **194 `src/` files need hand-merge**
  and 5,173 are under `test/` (largely sspec wave-6 oracle work — `26de1a115c3`
  is "wave-6 real oracles batch 11", so the clobber may have rewound a large
  regenerated corpus; unverified).
- The three entangled clusters above.

Nothing here should be read as "the clobber is contained". Roughly **6,324
affected paths remain** in the recorded baseline, against 129 repaired by this
PR.

## Method to continue

```sh
git worktree add --detach /path/wt origin/main
# still absent:
comm -23 <(git diff --diff-filter=D --name-only 4edef8fab8e~1 4edef8fab8e|sort) \
         <(git ls-tree -r --name-only origin/main|sort)
# still rewound: main blob == clobber blob != pre-clobber blob
# safe to restore iff pre-clobber is a strict superset:
diff <(sort now) <(sort pre) | grep -c '^<'   # 0 => additive-only restore
```

Verify every batch before landing: `cargo check --release --bin simple`,
`sh scripts/check/check-c-runtime-compiles-push.shs`, and
`bin/simple test test/unit/compiler`. Restores are entangled — expect a batch to
surface a missing companion rather than to apply cleanly.
