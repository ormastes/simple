# `io_runtime.read_file` still aborts the process — the 2026-08-23 fix was incomplete

**Date:** 2026-08-24
**Severity:** HIGH (process abort on the first read of any file, from a single import)
**Status:** OPEN
**Extends:** `doc/08_tracking/bug/seed_file_read_infinite_recursion_stack_overflow_2026-08-23.md` (fix `1ca19a1e31a`) — that fix is real but did not close the hole.

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
