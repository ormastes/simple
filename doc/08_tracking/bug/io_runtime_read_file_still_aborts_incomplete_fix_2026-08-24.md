# `io_runtime.read_file` still aborts the process — the 2026-08-23 fix was incomplete

**Date:** 2026-08-24
**Severity:** HIGH (process abort on the first read of any file, from a single import)
**Status:** ROOT-CAUSED 2026-08-25 — no source defect; stale stdlib baked into the deployed seed (see "Root cause and fix")
**Extends:** `doc/08_tracking/bug/seed_file_read_infinite_recursion_stack_overflow_2026-08-23.md` (fix `1ca19a1e31a`) — that fix is real but did not close the hole. **Superseded 2026-08-25:** the "hole" was a stale pre-fix stdlib copy loaded by the deployed seed, not an unclosed cycle — see "Root cause and fix".

## Reproduced independently, at the current tip

```console
$ cat v1b.spl
use std.io_runtime.{read_file}
fn main():
    print("LEN=" + read_file("README.md").len().to_text())

$ bin/simple run v1b.spl
fatal runtime error: stack overflow, aborting   (core dumped)
```

Three lines, ONE import, no `src/app` involvement and no second module pulled in
by hand. `1ca19a1e31a` rerouted `read_file`/`read_file_text` through
`file_read_result`, whose name has a single definition tree-wide, and that
genuinely fixed the *known* cycle — but the abort survives, so a second cycle
closes through `io_runtime`'s own import closure.

## Additional measurements

From a census run over 9,754 `.spl` files / 57,191 top-level definitions
(scratch only, nothing written to the repo):

- `use std.io_runtime.{file_read}` — aborts alone
- `use std.io_runtime.{read_file}` — aborts alone
- `use std.io_runtime.{read_file_text}` — aborts alone
- `use std.io_runtime.{file_read_result}` — works (one definition tree-wide)
- `use std.io.file_ops.{file_read}` — works
- `use std.fs.{read_file}` — works

So every `io_runtime` text-read entry point is still a process abort, and only
`file_read_result` escaped. `read_file_text` has just two definitions
(`io_runtime.spl:176`, `compiler/90.tools/leak_check/growth_runner.spl:24`) and
still overflows, so the surviving loop was not pinned statically.

**Correction to a claim in the earlier record:** the "second live example"
described there — a script importing both `std.common.sdn.parser.parse` and
`std.io_runtime.read_file` — is a red herring. `use std.common.sdn.parser.parse`
alone is fine; `std.io_runtime.read_file` alone aborts. The sdn import was
never part of it.

## Collision census — context, with its own limits stated

- 5,677 names are defined in more than one file, but **3,186 (56.1%) are
  layer-sibling clones** (the same relative path under `nogc_sync_mut/`,
  `nogc_async_mut/`, `gc_async_mut/`, `common/`), which are essentially never
  co-imported. A raw duplicate-name count is therefore ≥56% benign by
  construction and must not be quoted as a defect count.
- Ground truth check passed: with `io_runtime.spl` reverted to `1ca19a1e31a~1`
  the census re-derives the original cycle exactly
  (`file_ops.spl:76 file_read → read_file_text @ io_runtime.spl:163 → file_read`).
- 38 depth-2 candidate pairs survived filtering. **Four were probed and none
  reproduced**, so the static shortlist over-predicts: whether a collision binds
  wrongly depends on closure composition, which cannot be settled statically.
  Highest-risk unprobed clusters, both mutually recursive on BOTH sides (a wrong
  bind is unbounded recursion, not a one-hop wrong callee):
  `eval_expr`/`eval_binary`/`eval_unary`/`eval_call`/`eval_block`/`eval_field_access`
  (`compiler/10.frontend/core/interpreter/eval*.spl` vs
  `lib/gc_async_mut/pure/evaluator.spl`), and
  `convert_flat_expr`/`convert_flat_stmt`
  (`compiler/70.backend/backend/compile_c_entry.spl` vs
  `compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`).
- Depth was capped at 2, which covers both known incidents but not deeper cycles.

## Resume

- **Owner:** stdlib/io lane, with the compiler resolver lane for the general rule.
- **Repro:** the three-line script above. It needs no special environment.
- **Next step:** trace `io_runtime`'s import closure at runtime rather than by
  grep — the static approach found the first cycle and cannot find this one.
- **Done when:** that script prints a length, and a fixture pinning it runs in a
  gate (no spec can cover it: a stack overflow aborts the runner).

## Root cause and fix (2026-08-25)

**There is no second cycle.** `1ca19a1e31a` is complete in source. The abort
reproduced here is the ORIGINAL cycle, executed out of a **stale copy of the
stdlib that the deployed seed binary loads instead of the tree it is run
from.** Every "fix must be incomplete" inference above rested on the
assumption that `bin/simple run` reads `src/lib/**` from the current tree.
For this binary and this probe it does not.

### Evidence (runtime, not grep)

Binary under test (unchanged throughout):
`bin/simple -> /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
60650360 bytes, mtime 2026-08-23 04:47:05 +0000. `strings` shows its build
tree is `/mnt/data/worktrees/seed-deploy-1`. (Correction: `strings` on the ELF finds **0** such path literals, so the path is discovered at runtime, not compiled in. The evidence is the strace opens — independently reproduced: 20 opens under `seed-deploy-1/src/lib` alongside 316 under the current tree in one run.)

1. **`strace -e openat` of the three-line repro** (probe file in a scratch
   dir): the first `.spl` opens after the entry file are
   `/mnt/data/worktrees/seed-deploy-1/src/lib/io_runtime.spl`,
   `.../nogc_sync_mut/io_runtime.spl`, `.../io/process_ops.spl`,
   `.../io/process_governor.spl`, `.../io/signal_stubs.spl`,
   `.../io/file_ops.spl` — and only THEN the same six files from the tree the
   command runs in. 350 `src/lib` opens total; every module of the closure is
   flattened twice.
2. **That copy is pre-fix.** `git hash-object` of
   `seed-deploy-1/src/lib/nogc_sync_mut/io/file_ops.spl` is
   `63daa4a85259…` = `1ca19a1e31a~1:…/file_ops.spl` exactly (post-fix blob is
   `7b0e1e2ca52a…`); `…/io_runtime.spl` is `4528d1e336fb…` =
   `1ca19a1e31a~1:…/io_runtime.spl`. `git merge-base --is-ancestor
   1ca19a1e31a f421d425e34` (seed-deploy-1 HEAD) is **false** — that tree was
   never rebased onto the fix. So the loaded text is literally
   `file_ops.spl:76 file_read -> read_file_text(path)` and
   `io_runtime.spl:163 read_file_text -> file_read(path)`.
3. **`SIMPLE_DUMP_MIR=1` on the abort** (post-inline MIR, the last stage
   before Cranelift): `file_read` is a 14-line body whose only call is
   `Pure("file_read")` — itself — and `read_file`, `read_file_text`,
   `file_read_text` are 2054-line bodies of 256 `LocalAddr/Store/Copy/Jump`
   levels ending in `Call Pure("file_read")`. That is
   `codegen/mir_inline.rs` (`MAX_INLINES = 256`) unrolling
   `file_read -> read_file_text -> file_read -> …` until its cap and leaving
   the residual self-call; `compile_all_functions` had already collapsed the
   two `file_read` definitions to one (first-definition-wins, name-keyed).
   The 16-byte frames gdb shows (`push rbp; call self`) are that residual.
4. **The same dump with the probe INSIDE the tree** (so the resolver uses
   this tree's `src/lib` — and, note, `src/std`, the symlink, as a second
   root) lowers all four to a real 46-line `match` calling the unique
   `file_read_result`, and prints `LEN=46231`.
5. **Five other deployed seeds** whose baked build tree carries the fix
   (`lane-poll-unwrap`, `phase1full-1`, `startup-1`, `perfmem-1`,
   `toolbuild-1`; checked by blob id) all print `LEN=46231` for the identical
   scratch-dir repro; on `lane-poll-unwrap` (the one seed also probed with the
   single-import variants) `{file_read}` and `{read_file_text}` alone print
   `LEN=46231` as well.
   `use std.io_runtime.{file_read_result}` "works" on the stale seed only
   because both copies of that function have the same body.

Why the resolver ends up in another tree: the entry file lives outside any
project root (`find_project_root` looks for `src/` or `Cargo.toml` upward,
`interpreter_module/path_resolution.rs:360`), so the search-root list falls
back to roots derived from the build tree and the flattened module contains
BOTH trees' copies; the Cranelift `compile_all_functions` dedupe keeps the
FIRST definition of each name, which is the stale one. That is a defect in
its own right (a `bin/simple` should never read another checkout's stdlib),
filed for the resolver lane below — but it is not a stdlib cycle.

Two corrections to the method notes above: `SIMPLE_INTERPRETER_CALL_TRACE`
prints nothing for `run` because `run` goes through the Cranelift JIT, not the
tree-walking interpreter, so the "no Simple frame ever entered" reading was a
category error; and `SIMPLE_MAX_RECURSION_DEPTH` does not fire for the same
reason — the recursion is native JIT code, not interpreter frames.

### Fix

- **Source:** nothing. `src/lib/nogc_sync_mut/io_runtime.spl` and
  `io/file_ops.spl` at `origin/main` already route every text-read entry
  point through the uniquely-named `file_read_result`, and the MIR oracle in
  (4) proves the flattened result is acyclic under the JIT.
- **Deployment (the actual defect):** redeploy
  `bin/release/x86_64-unknown-linux-gnu/simple` from a tree at or after
  `1ca19a1e31a`, or rebase `/mnt/data/worktrees/seed-deploy-1` onto `main`
  first. Not done here — that tree belongs to another lane. Until then any
  probe run from outside a project root, and `bin/simple test` itself
  (the stale seed rejects the tree's `unsafe(...)` blocks with
  `error[E1002]: function 'unsafe' not found` before running a single spec),
  reports the seed-deploy-1 checkout, not `main`.
- **Regression pin:** `test/01_unit/lib/nogc_sync_mut/io/io_runtime_read_file_jit_probe.spl`,
  picked up by `scripts/check/check-runnable-probes.shs` (`*_jit_probe.spl`
  glob, scored on `interpret` and `jit`, a signal death is FAIL). A spec
  cannot pin this: the overflow kills the runner and specs never execute
  under the JIT. Failing-first evidence: the same probe file copied to a
  scratch dir and run by the stale seed exits 134 (`Aborted`); in-tree, and
  on every post-fix seed, it prints `PROBE VERDICT: PASS`. Caveat stated
  rather than hidden: on the current seeds the probe's `jit` lane is demoted
  to the interpreter (`[engine-demotion] reason=hybrid-interp-splice
  detail=rt_shell_exec` on post-fix seeds; `unresolved identifier 'ffi'` in
  `env_get` on the stale one), because importing `std.io_runtime` pulls in
  externs the JIT cannot splice. The gate still turns red on any seed whose
  JIT does compile the closure and overflows, which is the incident shape.

### Follow-ups (filed here, owned elsewhere)

- Resolver lane: `simple run <file outside a project root>` must not load
  `src/lib` from the binary's build tree, and must never flatten the same
  module from two roots (`src/lib` + `src/std` symlink is a second instance
  of the same double-load, in-tree). Both copies are byte-identical today
  only by luck.
- The seed's name-keyed, first-wins function dedupe in
  `codegen/common_backend.rs::compile_all_functions` is the general mechanism
  (`compiler_cross_module_private_symbol_collision`); `SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1`
  lists 16 same-signature collisions in this closure alone
  (`file_read`, `file_write`, `file_exists`, `process_run`, `shell`, …).
