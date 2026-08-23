# Developer-tooling latency audit — 2026-08-23

Lane: tooling latency (lint / test / startup). Worktree `/mnt/fast/wt-tooling-1`
at `origin/main` `e1f31f31da9`.

## Binary identity (mandatory with every timing)

| role | path | size | mtime | md5 |
|---|---|---|---|---|
| baseline (deployed seed) | `bin/release/x86_64-unknown-linux-gnu/simple` | 60,536,008 | 2026-08-22 15:29:00 | `51cd42a27916f8d36f02f31d31fbe390` |

Host state during measurement: 32 cores, load average 43-53, 24-27 GB available.
Absolute wall numbers are therefore an ENVELOPE (an idle box is faster); the
ratios and the syscall counts are load-independent and are the load-bearing
evidence.

## Target 1 — `bin/simple lint`

### 1a. The documented superlinear term no longer reproduces

`.claude/rules/commands.md` and
`doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md` record
`src/compiler/50.mir/hwir/zca_rows.spl` (1,901 lines, 30 heavy row-builder
functions) as **">2400s (killed) — exceeds any practical budget"**, and a
2-function prefix at ~210s.

Re-measured on the binary above, same file, boundary-aligned prefixes of the
same source:

| fixture | lines | top-level fns | wall | max RSS |
|---|---|---|---|---|
| trivial 1-fn | 2 | 1 | 37.9s | 397 MB |
| zca prefix | 48 | 1 | 36.4s | 400 MB |
| zca prefix | 293 | 5 | 39.2s | 390 MB |
| zca prefix | 633 | 10 | 39.1s | 391 MB |
| zca prefix | 1,170 | 16 | 37.0s | 450 MB |
| **`zca_rows.spl` FULL** | **1,901** | **30** | **44.3s** | **587 MB** |

All runs printed `Lint passed: all files clean`, so this is real work, not an
early bail.

**Conclusion: the superlinear term is gone.** The full file went from
`>2400s (killed)` to `44.3s` — a **>54x** improvement — and the per-content
slope across 2 -> 1,901 lines is ~6.4s total, i.e. roughly **flat**. The
`2026-08-18` seed redeploy (env-cache + parser fixes) that the rules file
already flags as invalidating the old table did in fact remove it. The old
per-declaration cost table in `.claude/rules/commands.md` is now stale in the
other direction as well: content complexity no longer dominates.

**What actually dominates lint today is FIXED STARTUP: ~37s of the 44s.**

### 1b. Located: the startup cost is redundant import-probe file reads

`strace -e trace=openat` on a lint of a **two-line** file:

- **3,819 successful `openat` of `.spl` files**, ZERO `ENOENT`
- over only **423 unique files** — a **9.0x open amplification**
- `src/compiler/10.frontend/core/ast.spl` opened **866 times**;
  `core/tokens.spl` **848 times**; `core/types.spl` 191; `core/parser.spl` 147
- weighted by file size: **67.7 MB read for 5.1 MB of distinct content —
  13.3x read amplification**

Every one of those reads is a full `fs::read_to_string` + UTF-8 validation, and
each is followed by a substring scan or a whole-file tokenize.

### 1b-i. First attribution attempt — WRONG, and recorded as such

The obvious suspects were the two import-resolution probes in
`interpreter_module/module_loader.rs`, `sibling_might_define_requested_names` and
`file_plausibly_provides_names`: both read the whole sibling file and scan it,
both were uncached across call sites, and both re-run per importing module. They
were memoized (`module_cache::probe_source_cached`, per process). The memo works
— pinned by unit test — but **the openat count did not move at all: still 3,819,
still 866 for `ast.spl`.** Those probes were not the source.

This is recorded rather than quietly dropped because it is the trap: the code
LOOKS like the defect, a fix for it is easy to write, and a wall-clock A/B on a
box at load 40+ is too noisy to refute it (the first A/B showed a 1-4s
"improvement" that was pure noise). Only the syscall count settled it.

### 1b-ii. Real attribution — call-site read trace

`perf`/attach profiling is blocked here and the deployed seed's own sampler is
dead (see 1d), so a minimal in-process attribution was added instead:
`src/compiler_rust/compiler/src/read_trace.rs`, gated on `SIMPLE_READ_TRACE=1`,
printing one `[read] <file>:<line> <path>` per source read. Kept in tree: this
lane is the second to be defeated by having no attribution, and the mechanism is
one atomic load when off.

Trace on a lint of the same two-line file — 3,522 traced reads:

| call site | reads | of which `core/ast.spl` |
|---|---|---|
| `hir/lower/import_loader.rs:700` `preregister_imported_type_names` | **2,672** | 749 |
| `hir/lower/import_loader.rs:855` `load_imported_types` | **611** | 121 |
| `hir/lower/import_loader.rs:291` `file_might_define_requested_symbol` | 145 | — |
| `hir/lower/import_loader.rs:758` | 92 | — |
| `hir/lower/import_loader.rs:646` | 2 | — |

Every traced read comes from the **HIR import loader**, not the interpreter's
module loader. And these two sites do not merely read — each does

```
read_to_string -> CRLF normalize -> Parser::new -> parser.parse()
```

on **every `use` statement that names the module**. `core/ast.spl` was fully
parsed 870 times for a two-line input. Both sites consume the result immutably
(`&imported_module.items`), and parsing is a deterministic function of the
file's bytes, so the repeat work is pure waste.

`O(importers x named-modules x parse-cost)`, driven by the COMPILER's own import
graph rather than by the file being processed — which is exactly why the trivial
fixture and the 1,901-line fixture cost nearly the same, and why this taxes
`test` and `run` as much as `lint`.

### 1c. Fix implemented

Two per-process memos, both keyed by resolved path:

1. `hir::lower::import_loader::parsed_imported_module()` — memoizes the **parsed
   module** (`Arc<Module>`). `None` memoizes "unreadable or unparseable", which
   both sites previously recomputed on every visit. This is the fix that matters.
2. `module_cache::probe_source_cached()` — memoizes probe file CONTENT for the
   loader's name probes. Kept: it is correct, it removes real duplicate reads on
   other paths, and it now also backs `file_might_define_requested_symbol`.

Both are cleared by `clear_module_cache()` alongside every other loader cache.

Semantics preserved: same bytes in, same AST out, same decisions. No change to
value semantics, COW, SFFI contracts, the `rt_*` ABI, or MDSOC layering. The
memos are **per process only** — deliberately NOT an on-disk cache — so a
`src/lib/**` edit is still picked up by the very next run and the load-bearing
"edit stdlib, no build needed" property in `.claude/rules/commands.md` is
untouched.

### 1c-i. Post-fix measurement

Binary under test: `simple_v2`, built from this worktree,
md5 `e82d52cccd917b71c23309308971b128`. Baseline is the same deployed seed as
above. Interleaved runs (old, new, old, new ...) so both sides see the same
load; the box drifted from ~38s to ~24s for the SAME baseline binary between
batches, which is precisely why only within-batch comparison is quoted.

Deterministic, load-independent — the load-bearing evidence:

| metric (trivial 2-line lint) | pre-fix | post-fix |
|---|---|---|
| successful `.spl` `openat` | 3,819 | **676** (5.65x fewer) |
| distinct files | 423 | 423 (unchanged) |
| `10.frontend/core/ast.spl` opens | 866 | <= 4 |
| verdict | `Lint passed` | `Lint passed` |

Wall clock and RSS, 3 interleaved repetitions, median:

| fixture | binary | wall (3 runs) | median | max RSS |
|---|---|---|---|---|
| trivial 2-line | baseline | 23.76 / 24.18 / 24.38 | 24.18s | ~410 MB |
| trivial 2-line | patched | 23.70 / 15.05 / 27.95 | 23.70s | ~517 MB |
| `zca_rows.spl` 1,901 | baseline | 33.86 / 23.94 / 35.79 | 33.86s | ~580 MB |
| `zca_rows.spl` 1,901 | patched | 24.45 / 21.38 / 31.79 | **24.45s** | ~691 MB |

Read honestly: on the heavy file the median improves **~28%**; on the trivial
file the change is **within noise** and no improvement is claimed. The variance
on this box (15.05s to 27.95s for identical work) is larger than the effect on
the small fixture, which is the whole reason the fix is pinned by COUNT.

**Cost, stated not buried: max RSS rises ~110 MB (+19-27%)** — the parsed ASTs of
423 modules are now retained for the process lifetime. That is a deliberate
trade of memory for parse work, it is bounded by the import closure (not by
input size), and it is the reason this must stay a per-process memo rather than
growing into a persistent cache.

### 1c-ii. Regression safety

`cargo test --release -p simple-compiler --lib`: **3,873 passed, 6 failed**.
The same **6** tests fail identically on a pristine `origin/main` checkout of the
same worktree (verified by reverting only `src/compiler_rust`, rebuilding, and
re-running exactly those test filters), so all 6 are pre-existing and none is
caused by this change:

- `hir::lower::tests::expression_tests::{text_rfind_uses_string_method_lowering,
  uppercase_string_is_empty_uses_string_method_lowering,
  impl_text_self_chars_index_remains_a_string_receiver}`
- `interpreter::interpreter_extern::tests::rt_string_ends_with_is_registered_and_correct_sdoctest_2026_08_07`
  (`rt_string_ends_with("héllo…", "o…")` returns true, expected false — a
  string-logic bug with no relation to module loading)
- `pipeline::native_project::tests::{test_core_c_lane_simple_lsp_mcp_startup_initialize_reduced_source,
  test_simple_core_source_tree_emits_partial_runtime_archive}` (both are the
  known missing-runtime-symbol lane: `rt_file_lock`, `rt_mmap`, `rt_struct_alloc`
  and friends)

The `hir::lower` three are named explicitly because they sit in the file this
change touches and would otherwise look like collateral; they are not.

## Target 2 — `bin/simple test` "Session setup"

`Session setup` is bracketed in `src/app/test_runner_new/test_runner_main.spl`
between `session_setup_start` (line ~246) and `session_setup_end` (line ~389):
test discovery, manifest indexing, and change-detection cache load. It already
emits per-phase `[setup] <phase>: begin` markers, added 2026-08-17 after three
lanes mistook the silence for a hang.

Note the structural point that the audit adds: `simple test` is itself a `.spl`
application interpreted by the same seed, so it pays the **same** import-probe
startup tax measured in 1b BEFORE `session_setup_start` is even reached, and
again inside discovery. The 1c fix therefore also applies to `test`; how much of
the ~310s it removes is measured in the post-fix section below.

## Target 3 — precompiled stdlib surface

The stdlib being read as SOURCE every run is **not** the problem the rules file
implies it is. Of the 3,819 reads on a trivial lint, `src/lib/**` accounts for a
minority; the bulk is `src/compiler/10.frontend/**`, and the cost is
**re-reading**, not reading. Caching compiled stdlib artifacts would be a large,
risky change that breaks the load-bearing "edit `src/lib`, no build needed"
property, and it would not address the dominant term. **Recommendation: do not
pursue a precompiled stdlib surface for latency reasons.** Deduplicating reads
(1c) is strictly cheaper, strictly safer, and hits the actual cost.

## Ranked fix list

1. **(implemented) Memoize the parsed imported module in the HIR import loader.**
   3,819 -> 676 opens on a trivial lint, `ast.spl` parsed 870x -> 1x, ~28% median
   wall on the heavy fixture, at ~110 MB RSS. Two call sites, per-process, no
   on-disk cache, no semantic change.
   **(also implemented, smaller)** Memoize the interpreter's probe reads — correct
   and kept, but measured NOT to be the dominant term.
2. **Rebuild + redeploy the seed so `SIMPLE_INTERP_SAMPLE` / `SIMPLE_LOADER_TRACE`
   actually work.** Every future latency investigation on this host is blind
   without them, and two prior attempts at target 1 were defeated by exactly
   this. Low risk, pure instrumentation.
3. **Correct the stale cost table in `.claude/rules/commands.md` and the lint bug
   record.** The documented ">2400s, exceeds any practical budget" figure is off
   by 54x and is actively misrouting work (this lane was briefed to hunt a
   superlinear term that no longer exists).
4. **Re-derive `scripts/check/check-lint-cost-budget.shs` thresholds** against
   post-fix reality; a budget calibrated to the pre-fix regime cannot detect a
   regression that lands anywhere under it.
5. **(deferred, needs design) Dependency-aware partial rebuild.** Unchanged from
   `.claude/rules/commands.md`: `interface_digest_of`, `simple.sdn` traversal and
   `smf_manifest_entry_verifies` all still have zero call sites. Out of scope
   here; not a latency fix for the interactive path.
6. **(rejected) Precompiled stdlib surface.** See Target 3.
