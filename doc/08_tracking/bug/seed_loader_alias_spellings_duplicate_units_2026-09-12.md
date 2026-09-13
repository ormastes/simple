# Seed loader: alias spellings of one file became separate loader units (2026-09-12)

Status: FIXED for the three raw-keyed sites. Two larger sibling findings, both
uncovered while measuring this one, are filed at the bottom and NOT fixed here.

Base: `28a96c436b9`, worktree `/home/yoon/dev/simple-loader-dedup`.
Entry measured throughout: `src/app/mcp/main.spl` (`run … --help`).

| binary | path | size | mtime |
|---|---|---|---|
| seed (before) | `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` | 50,093,192 | 2026-09-06 09:59:11 |
| candidate (after) | `<worktree>/src/compiler_rust/target/release/simple` | 51,262,160 | 2026-09-12 12:16:41 |

## The defect

`src/std` is a symlink to `lib` and `src/compiler/common` to `00.common`, and the
module resolver emits both relative and absolute spellings of the same path. Three
loader caches were keyed by the RAW spelling, so one physical file became several
loader units — an extra read plus a full re-parse per alias, and the same types
registered more than once into the HIR lowerer:

| site | cache | keyed by |
|---|---|---|
| `src/compiler_rust/compiler/src/hir/lower/import_loader.rs:39,56` | `IMPORTED_MODULE_AST` (parsed-AST memo) | raw path |
| `src/compiler_rust/compiler/src/hir/lower/import_loader.rs:877,898,902,908,963` | `loaded_import_targets`, `loaded_modules` | raw `resolved.path` |
| `src/compiler_rust/compiler/src/module_resolver/manifest.rs:187,205` | `ModuleResolver.manifests` | raw `init_path` |

The interpreter's own module cache was **already correct**: `get_cached_module_exports`
/ `cache_module_exports` (`module_cache.rs:409,421`) key through `normalize_path_key`,
which canonicalizes. That function is the fix's kernel — the three sites above now
use it too.

## Measured, before → after

Attribution via `SIMPLE_READ_TRACE=1` (`read_trace.rs`, one `[read] <file>:<line> <path>`
line per source read), realpaths resolved per site.

| site | before | after |
|---|---|---|
| `import_loader.rs` parse memo | 120 reads, 120 spellings, **117 physical** | 117 reads, 117 spellings, 117 physical |
| (the memo's read site moved `import_loader.rs:44` → `:52` when the doc comment grew — same site, not a vanished one) | | |
| `interpreter_module/module_loader.rs:980` | 128 reads, 128 spellings, 128 physical | unchanged |
| `IMPORT_AST_PARSES` (`SIMPLE_PERF_COUNTERS=1`) | **120** | **117** |

Three files were parsed twice — `src/app/mcp/assistant/session_store_helpers.spl`,
`src/app/mcp/assistant/types.spl`, `src/app/mcp/main_lazy_json.spl` — each under an
absolute and a relative spelling: **41,134 bytes** of avoidable re-parse.

MCP startup, `/usr/bin/time -f '%e %M'` x7 **interleaved** seed/candidate (a
sequential A-then-B on this box is worthless: an unpaired run measured the
candidate at 7.71 s p50 purely because a test suite was running beside it). Load
average 47.6, 83 users:

| binary | wall p50 | wall spread | RSS median |
|---|---|---|---|
| seed | 6.45 s | 3.62 – 9.96 s | 295,592 KiB |
| candidate | 5.94 s | 4.65 – 8.87 s | 295,056 KiB |

The 0.51 s wall and 536 KiB RSS differences are far inside a 3.6–10 s spread.
**No wall-time or memory claim is made**, and none should be: three parses of
41 KB out of ~2.4 MB cannot be resolved on this host. The value of this change is
the correctness of unit identity, not speed.

## Correction to the triage that requested this

The finding was filed as "239 loader units for 131 physical files — 108 alias
duplicates, ~1.13 MB re-parsed", derived from `strace -f -e trace=openat` counting
distinct `.spl` path spellings. Those raw numbers reproduce exactly (571 openat,
239 spellings, 131 physical, 108 duplicates, 1,133,132 bytes). **The interpretation
does not.**

1. **An openat spelling is not a loader unit.** Only 255 of the 571 opens are module
   source reads; the rest are the resolver's manifest probes and the JIT lane. Of the
   255, exactly **3** are alias-duplicate re-parses (41,134 bytes), not 108 / 1.13 MB —
   an overstatement of roughly 25x.
2. **The 108 "alias duplicates" are mostly CROSS-LANE, not mis-keying.** Each lane
   reads each file once: the HIR lowerer 117 physical files, the interpreter 128,
   intersection **117**, union 128. The two lanes simply reach the same file under
   different spellings (one via `src/std/…`, the other via `src/lib/…`), and a census
   over spellings cannot tell that apart from a keying bug.
3. **The corroborating symptom is a different defect class.** `public function
   'process_wait' has 3 co-compiled definitions` is emitted by
   `pipeline/module_loader.rs:1754`, which already canonicalizes (`:2237`), and every
   such warning says *"with 2 differing signatures"* — `process_wait (i64)->i64` vs
   `(i64,i64)->i64`, `shell (text)->ProcessResult` vs `(text)->i64`. Identical-signature
   duplicates are explicitly not reported (`:1692`). These are genuine cross-module
   name collisions, unrelated to alias spellings, and the fix does not change them.

## Sibling findings — real, larger, NOT fixed here

- **Dual-lane parsing (the actual startup opportunity).** Every one of the 117 files
  the HIR lowerer parses is parsed AGAIN by the interpreter: **1,265,979 bytes parsed
  twice**, in two caches that never share (`IMPORTED_MODULE_AST` vs
  `MODULE_EXPORTS_CACHE`). This is what N's 1.13 MB was actually measuring. Sharing an
  AST across those lanes is a design change, not a keying fix.
- **JIT lane re-reads.** Default (JIT) mode opens 571 `.spl` files where interpreter
  mode opens 310. `pipeline/module_loader.rs` canonicalizes correctly (`:2026,2074,2237`)
  but has no parse memo, so it re-reads source per traversal.
- **`variants/__init__.spl` read 49 times** by `module_resolver/var_overlay.rs:110`
  (`read_group_order`), un-memoized. Only 1,309 bytes, so it is cheap — but it is 49
  syscalls for one constant. Now visible: that read site was untraced before this
  change and is wired into `read_trace` here.
- **`import_loader.rs:830`** (package sibling scan) reads one file 7 times.

## Gate

`scripts/check/check-loader-unit-identity.shs` — fail-closed, `--selftest` runs first
and is fatal (7 fixtures: clean must PASS; symlink alias must FAIL; relative-vs-absolute
must FAIL; the same spelling read many times must PASS, because a missing memo is a
different defect; one file read at two DIFFERENT sites must PASS, because that is the
cross-lane finding above; a one-site trace must report 1 site; an empty trace must
report 0 reads). Verdict is the last stdout line: `PASS — <n> read(s) checked across
<k> site(s), 0 alias-duplicate unit(s)` exit 0 / `FAIL` exit 1 / `ERROR — nothing was
checked` exit 2.

**The gate clears `SIMPLE_EXECUTION_MODE` for its traced run and refuses to pass on
fewer than 2 loader sites.** This was not defensive programming: the first version
was PASS-vacuous under the spec runner, which exports
`SIMPLE_EXECUTION_MODE=interpreter`. That mode skips HIR lowering entirely, so only
the interpreter's already-correct cache is exercised — 1 site, 128 reads, 0 offenders,
a green over the exact cache the defect lives in. Verified: the seed now FAILs through
the gate under that same env.

Red → green on real traces:

```
seed      FAIL — 255 read(s) checked across 3 site(s), 3 alias-duplicate unit(s)
candidate PASS — 301 read(s) checked across 4 site(s), 0 alias-duplicate unit(s)
```

(301 > 255 because this change wires `var_overlay.rs` and `resolution.rs` into the
read trace; reads did not increase, attribution did.)

Spec: `test/05_perf/startup/loader_unit_identity_spec.spl`.
Mechanism rows: `scripts/check/check-perf-regression-tests.shs`, `LOADERUNIT *` (9 rows,
`ROW_FLOOR` 147 → 156 — raised by exactly the number of rows added, per that
guard's own rule; the pre-existing 147-vs-191 gap is another lane's to close).
That guard was already FAIL at base `28a96c436b9` with 4 regressed rows
(`pure-interp array push through owner`, `HOPPARK test pins clone budget at every
depth`, `ANYVTJIT seed: aggregate copy keeps vtable hdr`, `IMPORTASTMEMO seed: memo
cleared with the loader caches`); all four were verified red against the base blobs
and none is touched by this change. The 9 new rows are `ok`.
Rust unit test: `hir::lower::import_loader::tests::alias_spellings_of_one_file_are_one_parsed_unit`
— object identity (`Arc::ptr_eq`) across a symlinked and a `.`-relative spelling.
RED before the fix (panic at the `via_symlink` assert), GREEN after.

## Suites, seed vs candidate

`cargo test --release -p simple-compiler --lib` filtered: `module_` 169/0,
`import_` 42/0, `resolve` 114/0, `loader` 80/0, `hir::lower::import_loader::tests`
9/0, and the pre-existing memo pin
`imported_module_ast_memo_tests::repeated_import_of_the_same_module_parses_it_exactly_once`
1/0 — the one test that could have been broken by re-keying the memo.

`bin/simple test <dir>`, seed and candidate, **identical counts in all three**
(the failures are pre-existing and unchanged by this fix):

| suite | seed | candidate |
|---|---|---|
| `test/01_unit/compiler/loader` | 272 total, 201 passed, 71 failed, 50 skipped | identical |
| `test/01_unit/compiler/module_resolver` | 65 total, 60 passed, 5 failed, 2 skipped | identical |
| `test/01_unit/language` | 182 total, 176 passed, 6 failed, 5 skipped | identical |

`module_resolver` is the suite that would have caught a behaviour change from the
canonical manifest key (a `__init__.spl` reached under two spellings now yields the
first spelling's parsed manifest for both); it does not move.
