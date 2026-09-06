# `std.io_runtime.file_write` resolves to a retryless twin — silent write failure into a missing directory

**Filed:** 2026-09-06 (lane C, found by the dual_fs effect-comparison harness)
**Severity:** high — a write returns `false` and creates nothing, in a code
path that carries explicit repair logic for exactly that case.
**Status:** OPEN. Not repaired here: the fix changes stdlib dispatch that other
lanes call.

## Symptom

Writing into a directory that does not exist fails and creates nothing, even
though `std.io_runtime.file_write` (`src/lib/nogc_sync_mut/io_runtime.spl:221`)
contains a parent-directory create-and-retry tail written for precisely this
case (lines 227-243, referencing the earlier bug
`interp_examples_dir_f64_zero_and_write_noop_2026-07-03`).

Measured on `bin/simple` (aarch64 seed), repo worktree, `build/probe7_x`
absent:

```
$ bin/simple run build/scratch/probe7.spl
std.io_runtime.file_write -> false exists=false
captured-retry version:
  dir_create_all(build/probe7_y)=true retry=true
captured-retry -> true exists=true
```

The second block is a **local** function in the same file containing the same
logic. It succeeds. `build/probe7_x` was never created, so the retry tail in
`io_runtime.file_write` did not merely fail — it never ran.

## Root cause

The function registry is keyed on **name alone**. `file_write(path: text,
content: text) -> bool` is defined **10 times** under `src/lib`, and at least
two of those definitions have the same signature as `io_runtime`'s and **no
retry policy at all**:

| Definition | Body |
|---|---|
| `src/lib/nogc_sync_mut/io_runtime.spl:221` | write, then create parent + retry |
| `src/lib/nogc_sync_mut/database/atomic.spl:39` | `rt_file_write_text(path, content)` — no retry |
| `src/lib/nogc_async_mut/io/mod_stub.spl:29` | `file_delete` then `rt_file_write_text_at(...) >= 0` — no retry |

`use std.io_runtime.{file_write}` therefore does not guarantee that
`io_runtime`'s definition is the one called. The observed behaviour — returns
`false`, no directory created, no retry — matches `database/atomic.spl:39`
exactly and matches `io_runtime.spl:221` not at all.

The interpreter already warns about this class on every run of this tree, for
other symbols:

```
warning: public function `env_get` has 4 co-compiled definitions with 2 differing
signatures ...; JIT call sites resolve by exact arg-type match (mangled `$dupN`
variants), falling back to the last definition when types are ambiguous — a
fallback hit may still dispatch to the wrong one.
[compiler_cross_module_private_symbol_collision]
```

Here the signatures are **identical**, so the "exact arg-type match"
disambiguation has nothing to discriminate on and the choice is arbitrary.

## Why nothing caught it

The same reason as the two incidents that motivated the harness
(`std.file_system.file_write_text` mocking a write, and unregistered externs
returning nil): every existing check compares **return values** or **source
structure**. `check-dual-run-shadow.shs` and `std.common.spec.dual_run`
(`dual_check_f64` / `_text` / `_i64` / `_bool` / `_bytes`) compare returns; the
push-tier guards compare trees, symbol sets and compilability. A function that
returns a plausible `bool` and touches no disk is invisible to all of them.

It was found within minutes of pointing `dual_check_fs_effect` at the pair,
because the effect probe reads `exists` / `size` / `digest` / `mode` off the
filesystem after the call.

## Reproduction

`build/scratch/probe7.spl` in the lane-C worktree (scratch, not committed).
Minimal form:

```simple
use std.io_runtime.{file_write, file_exists}

fn main():
    val p = "build/does_not_exist_yet/a.out"   # parent absent
    print("{file_write(p, \"bytes\")} exists={file_exists(p)}")   # -> false exists=false
```

Ruled out as causes, each measured separately:

* `path.rfind("/")` returns 14 for `build/probe8_z/a.out` — correct.
* `host_path_native("build/probe9_q")` is identity, and `rt_file_exists` on it
  is `false` — so the `if parent_exists: return false` early-out is not
  legitimately taken.
* `rt_dir_create_all` and `rt_file_write_text` both work when called directly
  (`dir_create_all=true retry=true` above).

## Impact

Any caller writing a receipt, cache entry, artifact or log into a directory it
has not separately created gets `false` and no file. Because the sibling
`file_write_text` surfaces in `src/lib/*/file_system/file_ops.spl` return
`true` while writing nothing, the two failure modes are mirror images: one
lies about success, the other silently withholds a repair it advertises.

## Fix directions (not applied here)

1. **Rename the colliding definitions.** `database/atomic.spl` and
   `io/mod_stub.spl` should not export a symbol named `file_write` with
   `io_runtime`'s signature. This is the narrow, low-risk repair and matches
   the interpreter warning's own advice ("Rename the conflicting helper(s) to a
   unique name").
2. **Make identical-signature duplicates an error, not a silent choice.** The
   existing warning fires only when signatures *differ*; identical signatures
   are the more dangerous case and are currently silent.
3. **Effect-pair the write family** so a regression is caught by the gate
   rather than by a future incident — release R2 of
   `doc/03_plan/runtime/native_to_pure_simple/native_surface_to_pure_simple_migration.md`.

## Consequence already applied in this lane

`std.dual_fs.ensure_dir` exists so the harness creates its sandbox explicitly
and never leans on a writer's own retry — a fixture that depended on the
behaviour under test could not report on it. `fs_write_text_pure` restates the
parent-directory retry in pure Simple and is measured performing it
(`native returned=false exists=false` / `pure returned=true exists=true` on an
absent parent), which is why the pure provider is currently the *more* correct
of the two twins.
