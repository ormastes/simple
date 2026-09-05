# Why compiling one file pulls 778 modules — measured, 2026-08-24 (Lane W)

Binary measured: `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed),
60650360 bytes, mtime 2026-08-23 04:47:05. All numbers from strace ground truth.

## A) Duplication hypothesis: FALSE (2.67%, and none of it in the closure)

Content-hashed every `.spl` under `src/` with symlinks RESOLVED (vendor excluded):
- distinct real files: 15,264; total 111,988,455 bytes
- **exact duplicate bytes: 2,990,795 = 2.671%** (644 redundant copies)

All of it is the deliberate memory-model triplication in `src/lib`
(`nogc_sync_mut` / `nogc_async_mut` / `gc_async_mut`). **Only ONE of the three
trees (`nogc_sync_mut`, 82 modules) is in the compile closure at all**, so this
duplication contributes ZERO to closure size. Not a driver. No dedup work done.

Prior lane's "81 duplicate basenames" was noise, as warned: `__init__.spl` alone
is 161 paths, and 17 dirs under `src/compiler` are symlinks, not copies.

## B) What actually drives closure size

`bin/simple compile src/app/cli/bootstrap_main.spl`: 21.05 s, 1.5 GB RSS.
- **804 distinct `.spl` path spellings opened** (matches the reported 778)
- 986 total `.spl` openat calls (1.23x re-open; no ENOENT path probing)
- Failure is at the SEMANTIC phase, so the full parse of all 804 DID complete.
  **The ">1 hour parse phase" claim does not reproduce on this binary: 21 s.**

### Reachable vs referenced GAP
- reachable via `use` edges (strace, realpath-deduped): **747**
- modules with >=1 top-level definition referenced elsewhere in closure: **664**
- **GAP = 83 modules = 11.1%** (60 have no top-level defs at all — pure
  re-export/data; 23 are genuinely unreferenced)

So ~89% of the closure is genuinely referenced. The entry legitimately needs
the compiler pipeline.

### Barrel/wildcard hypothesis: FALSE
Only **12** `__init__.spl` barrels appear in the entire 747-module closure, with
**45** total re-export edges between them. Barrels are explicit symbol lists,
not wildcards. A controlled fixture confirms barrels cost something but the
population is far too small to matter:
- `use compiler.hir.{HirModule}` (barrel): 22 `.spl` opens
- `use compiler.hir.hir_types.{HirModule}` (deep): 11 `.spl` opens

### 57 of 804 loads are the same file under two path spellings (7.1%)
804 path spellings resolve to only **747 real files**: 57 files are opened twice
under two spellings, because `src/compiler/mir` is a symlink to
`src/compiler/50.mir` (17 such symlinks exist, because a numbered directory name
cannot be spelled in a dotted `use` path). Examples:
`50.mir/mir_instruction_graph.spl` + `mir/mir_instruction_graph.spl`;
`20.hir/hir_types.spl` + `hir/hir_types.spl`.

**Attempted fix, MEASURED AS A NO-OP, and REVERTED.** The import dedupe key is
`(resolved.path, import_target_cache_key(target))` at
`src/compiler_rust/compiler/src/hir/lower/import_loader.rs:816`, on a
non-canonicalized `PathBuf`. Canonicalizing that key (and the `loaded_modules`
cycle-guard key) looked like the fix. Built two binaries from one tree differing
only in that change and measured both:

| | path spellings | total .spl opens | co-compiled warns | wall |
|---|---|---|---|---|
| BEFORE (md5 cc2b37f1…) | 804 | 986 | 1 | 11.21 s |
| AFTER  (md5 b635fc6d…) | 804 | 986 | 1 | 16.68 s |

Wall times are SINGLE runs on a heavily contended shared box (the same compile
measured 21.05 s, 11.21 s and 16.68 s across this session) and carry no signal —
do NOT read the 11.21->16.68 row as a regression. The no-op verdict rests
entirely on the open counts and warning count being byte-identical.

Identical semantic output. **Zero effect**, so the redundant opens do NOT flow
through that dedupe key. The change was reverted rather than kept on plausibility.

Honest limit on this finding: strace proves 57 redundant *opens*, not 57
redundant *parses*. `file_might_define_requested_symbol`
(`import_loader.rs:620-660`) opens sibling files merely to scan them, so some of
these opens are cheap scans, not parses. The real origin of the alias-spelled
opens was not located.

## Seed build blockage (LOCAL STALENESS, not an origin bug)
The local worktree's Rust seed did not compile: `interpreter/dispatch_profile.rs` is
tracked and called from `interpreter/expr.rs:292`, but `mod dispatch_profile;`
was never added to `interpreter/mod.rs`, so
`cargo build --release --bin simple` failed with E0433. Measured rc=101 before,
**rc=0 after** adding the one missing `mod` line — which is how the two
measurement binaries below got built at all.

**Checked before claiming a fix: `origin/main` ALREADY contains
`mod dispatch_profile;`.** Another lane had already fixed it; this worktree was
merely stale (it has since diverged from origin by 9,584 files). So this is NOT
an upstream defect and nothing was landed for it — recorded only because it
blocked, and unblocked, the measurement.

## Verdict
- Duplication is a non-issue: 2.67% of bytes, and **zero** of it in the closure.
- Barrels are a non-issue: 12 in a 747-module closure, 45 re-export edges.
- The closure is **~89% genuinely referenced**; the 83-module gap (11.1%) is the
  hard ceiling on any loading-precision work, sibling-preloading included.
- The ">1 hour parse" premise did not reproduce: the entire 747-module closure
  parses in 11-21 s. The plausible reconciliation is per-invocation closure
  reload across ~692 separate stage-3 `compile` invocations (21 s x 692 ~ 4 h),
  i.e. no cross-invocation parse cache — NOT parse speed, NOT duplication.
  Not built here; recorded as the finding.
- **No code change is justified by any of these measurements, and none was
  landed.** The one change tried (canonicalized import dedupe key) measured as a
  no-op and was reverted; the seed `mod` line was already fixed at origin.
  This document is the entire deliverable.
