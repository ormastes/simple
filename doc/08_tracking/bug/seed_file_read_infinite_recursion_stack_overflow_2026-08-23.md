# `file_read` infinitely recurses and aborts the process — seed-dependent, any file

- Date: 2026-08-23
- Status: OPEN. Worked around at the one call site that hit it; the defect itself
  is unfixed and is a live landmine for every other caller.
- Severity: high — it aborts the process (`SIGABRT`, core dumped), it is not a
  wrong answer you can check for, and `file_read` is one of the most-used
  functions in the tree.

## Symptom

```
fatal runtime error: stack overflow, aborting
```

`rc=134`, core dumped, in under 9 s, with no other output.

## Minimal reproduce

```simple
use std.io_runtime.{file_read}
fn main():
    val s = file_read("/etc/hostname") ?? ""
    print "len={s.len()}"
```

| seed | result |
|---|---|
| `/mnt/fast/cargo-target-run20/release/simple` (2026-08-23 02:01) | **rc=134, stack overflow** |
| `bin/release/x86_64-unknown-linux-gnu/simple` (deployed) | rc=0, `len=3` |

**It is not procfs-specific.** The first reproduce used `/proc/meminfo`, whose
`st_size` is 0, which made a size-based read loop the obvious suspect — but a
plain regular file on a normal filesystem fails identically. Anyone triaging
this should not go looking for a pseudo-file special case.

## Where it comes from

`src/lib/nogc_sync_mut/io/file_ops.spl:76`

```simple
fn file_read(path: text) -> text:
    read_file_text(path)
```

`file_read` is a one-line forwarder to `read_file_text`. If `read_file_text`
resolves back to `file_read` in a given build, that is unbounded mutual
recursion with no base case, which is exactly the observed signature (stack
overflow rather than a hang or a wrong value). The same build emits

```
warning: public function `env_get` has 3 co-compiled definitions with 2 differing
signatures ((text)->Optional(text) vs (text)->text); JIT call sites resolve by
exact arg-type match ... falling back to the last definition when types are
ambiguous — a fallback hit may still dispatch to the wrong one.
[compiler_cross_module_private_symbol_collision]
```

so cross-module symbol collision with last-definition-wins fallback is already
known to be live in this build. `file_read` forwarding to a name that can
collide is the same class. **This has not been confirmed by reading the
resolved symbol table** — it is the leading hypothesis consistent with every
measurement, and whoever fixes it should confirm before changing dispatch.

## How it was found

It took down `main`. Commit `ff095d31591` added a `MemAvailable` clamp for shard
concurrency whose only new I/O was `file_read("/proc/meminfo")`, on the
`native-build` orchestrator path. Every `native-build` then aborted with
`rc=134` before step 0/6 — including a 3-line hello world with `--threads 2`, so
not load-dependent. Reverted in `765f9d2aad4`.

Bisect, by running (each step a real `native-build`, ~9 s to crash):

| variant | result |
|---|---|
| clamp as landed | rc=134 |
| module present, `shard_threads_mem_cap` body → `requested` | rc=124 (no crash) |
| full body, `/proc` read replaced by a constant | rc=124 (no crash) |
| **`file_read` called but its result discarded, never parsed** | **rc=134** |

The last row is the isolation: neither the clamp arithmetic nor the parser is
involved, only the `file_read` call. `SIMPLE_SHARD_MEM_CLAMP=0` also cleared it,
which is what first pointed at the clamp path rather than the 19 other commits
in the window.

## Workaround used

The clamp now reads MemAvailable via `process_run_timeout("awk", ...)` — the same
mechanism `native_build_main.spl` already uses for `readlink` on that exact path,
so it is proven live there. That is a workaround at one call site, **not a fix**.

## Why this matters beyond the clamp

`file_read` is called all over `src/` and `test/`. On any build where this
resolution goes wrong, every one of those call sites aborts the process. The
deployed binary is fine today, so the tree looks healthy; the defect surfaces
only when a particular seed is used, which is precisely how it consumed a
build-blocking incident before being identified.

## Suggested follow-up

1. Confirm the resolution hypothesis by dumping the symbol table for
   `read_file_text` / `file_read` in a build that reproduces.
2. Give the forwarder a unique callee name so it cannot collide, per the
   compiler's own advice in the collision warning.
3. Consider making `compiler_cross_module_private_symbol_collision` fatal for
   the case where a function's resolved callee is itself — self-recursion via
   fallback dispatch is never intended and is statically detectable.
