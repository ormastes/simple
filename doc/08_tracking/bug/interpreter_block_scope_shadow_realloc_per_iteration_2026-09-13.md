# Interpreter reallocated block-scope shadow names on every loop iteration

- Status: RESOLVED (2026-09-13)
- Lane: PERF-6, worktree `/home/yoon/dev/simple-perf-6`, base `origin/main` f26970e9d93
- Seeds: base sha256 `22878382bc1b5ccf...`, candidate `1b54d369561036e8...`

## What

`exec_block` (`src/compiler_rust/compiler/src/interpreter/block_exec.rs`) runs
`capture_node_scope_shadows` before and `restore_block_scope_shadows` after
EVERY block execution. For a loop body that is once per iteration, and a body
that declares a `val`/`var` is the most common loop-body shape in the stdlib:
**28,246** in-body declarations in `src/lib/common`, against 10,859 `[i]` reads
and 5,774 `.push(` calls.

Per declared name per iteration the capture allocated three owned copies of the
same name (`to_owned()` into a scratch `Vec<String>`, `clone()` into a dedup
`HashSet<String>`, `clone()` into the returned vector), plus the HashSet and the
scratch Vec; the restore allocated a fourth String and cloned an `Arc` to build
the `(owner, name)` pair its `CURRENT_EXEC_MODULE` fallback probed with, where
`source_name` was always `name.clone()`.

## Measurement

The isolating control pair is three body statements with the temporary hoisted
out of the loop vs. the same three statements with it declared inside, both at
n = 2,000,000.

**The headline number is child USER CPU time**, because wall clock on this host
does not survive its own control: an unchanged seed produced in-process ratios
of 0.846 and 0.963 for a shape that does strictly more work
(`perf_wall_clock_ratio_unmeasurable_on_loaded_host_2026-09-13.md`). Interleaved
A/B with `/usr/bin/time -f '%U %S'`, 6 reps each:

| control | CPU ms, median | CPU ms, min |
|---|---:|---:|
| temporary hoisted out of the loop | 1,840 | 1,400 |
| temporary declared in the body | 2,340 | 2,000 |

**The declaration cost ~250 ns/iteration by medians, ~300 by minima** -- about
20% of a ~1,170 ns/iteration generic walk.

The 12-shape wall-clock corpus, taken at load 35-40, put the same pair at 1,376
and 2,819 ns/iteration (a 1,443 ns overhead). Those figures are inflated by
roughly 1.4x against CPU time and are **not comparable across runs**; they are
retained only because the relative ORDER of the 12 shapes is stable under load,
which is what the corpus was used for. The one wall figure that is load-free by
construction is the matched control: `acc = acc + (i % 7)` with no declaration
runs at **10 ns/iteration** because a native while matcher takes it, which is
the separate 271x cliff filed as
`interpreter_val_decl_in_loop_body_declines_every_matcher_2026-09-13.md`.

## Fix

Names are borrowed from the AST (`Vec<(&'a str, Option<Value>)>`); the dedup
HashSet is replaced by a linear scan over the names collected so far (a block
declares a handful, and the rule "only the FIRST declaration of a name in a
block is captured" is preserved); the single-identifier declaration needs no
collection at all; both owner-store paths pass `name` straight through. One
owned String remains, the one `enter_block_local` hands to its map key.

Before/after on child USER CPU time, same harness as above: declaration overhead
**250 -> 152 ns/iteration** by medians, **300 -> 150 ns/iteration** by minima.
That is a 39-50% cut in the bookkeeping, i.e. roughly 8-13% off a whole
iteration of any loop body that declares a name -- a real win, not an
order-of-magnitude one.

Pinned by `test/05_perf/interp/block_scope_shadow_parity_spec.spl` (7 examples)
and 14 `BLOCKSHADOW` rows in `scripts/check/check-perf-regression-tests.shs`.

## Still open, deliberately not fixed here

`BLOCK_SHADOW_OWNER_PROBES` measured 3,000,006 against 3,000,031
`BLOCK_SHADOW_NAMES`: nearly every block-local temporary still pays a two-hash
lookup on the module-global store to learn that it is not a module global.
Skipping it needs a fact the capture side cannot establish more cheaply than the
probe itself, and the one behaviour the probe exists for is real -- see the
`sem_global_shadow.spl` fixture, where a callee mutates the shadowed global
mid-block and the post-block read must see the NEW value (`30:9`).
