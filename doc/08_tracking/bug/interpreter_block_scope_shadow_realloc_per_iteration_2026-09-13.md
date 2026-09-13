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

12-shape corpus at n=2,000,000 on the base seed. The isolating control pair is
three body statements with the temporary hoisted out of the loop vs. the same
three statements with it declared inside:

| control | ns/iteration | note |
|---|---:|---|
| `acc = acc + (i % 7)` (2 stmts) | 10 | matched a native while matcher |
| `t = i % 7; acc = acc + t; i = i + 1` | 1,376 | generic walk, no in-body decl |
| `val t = i % 7; acc = acc + t; i = i + 1` | 2,819 | generic walk, one in-body decl |

The declaration alone cost **1,443 ns/iteration** -- more than the whole rest of
a three-statement generic iteration.

## Fix

Names are borrowed from the AST (`Vec<(&'a str, Option<Value>)>`); the dedup
HashSet is replaced by a linear scan over the names collected so far (a block
declares a handful, and the rule "only the FIRST declaration of a name in a
block is captured" is preserved); the single-identifier declaration needs no
collection at all; both owner-store paths pass `name` straight through. One
owned String remains, the one `enter_block_local` hands to its map key.

Before/after on child USER CPU time (wall clock is unusable here, see
`perf_wall_clock_ratio_unmeasurable_on_loaded_host_2026-09-13.md`), interleaved
A/B, 6 reps each: declaration overhead **250 -> 152 ns/iteration** by medians,
**300 -> 150 ns/iteration** by minima.

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
