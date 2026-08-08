# BUG: baremetal externs have no interpreter binding — `unsafe_addr_of` and `rt_x86_syscall` fail closed in hosted unit specs

**Status:** OPEN
**Found:** 2026-08-04
**Severity:** medium — 3 confirmed failing examples in
`test/01_unit/os/posix/`. The failure is a hard error, so the affected
assertions never run.

> **Revision note (same day):** an earlier version of this report claimed
> `rt_string_char_at` was also unregistered and blamed 5 failures in
> `test/01_unit/fs_driver/` on it. **That was a measurement artifact** — the
> evidence was gathered without `--no-cache --no-cover-check`. Re-measured
> properly, `rt_string_char_at` **works**, and `mount_table_resolve_test.spl`
> passes 6/6 and `mount_table_test.spl` 13/13. The static census below was
> also weakened by the same discovery. Corrected in place; see
> "Census — unreliable, do not cite" for what that invalidates.

## Symptom

`bin/simple test` runs specs on the tree-walk interpreter
(`[mode: interpreter]`). Reaching an `extern fn` with no interpreter binding
kills the example with `semantic: unknown extern function: <name>`.

Verified with the mandatory flags:

```bash
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check \
    test/01_unit/os/posix
# Results: 109 total, 100 passed, 9 failed
#   FAIL fd_io_route_spec.spl   (10 passed, 2 failed)
#         Error: semantic: unknown extern function: unsafe_addr_of
#   FAIL signal_compat_spec.spl (8 passed, 1 failed)
#         Error: semantic: unknown extern function: rt_x86_syscall
#   FAIL fd_table_spec.spl      (14 passed, 6 failed)
#         Error: Process exited with code 1        <- different cause, not triaged
```

This run reproduced identically across two independent measurements, so these
two names are solid.

## Root cause

The interpreter's extern table is a Rust-side map built with `insert_simple!`
and siblings in `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`
(e.g. `mod.rs:1710` registers `rt_string_len`). A miss raises the error from
`src/compiler_rust/compiler/src/interpreter_extern/common/error_utils.rs:23`.

`unsafe_addr_of` and `rt_x86_syscall` have no registration. Both are
**baremetal primitives** — taking the address of a value, and issuing a raw
x86 syscall. Neither has a meaningful hosted implementation, which is the
substantive issue: these specs exercise kernel code from a hosted interpreter
that structurally cannot run it.

## Census — unreliable, do not cite

An earlier static diff of "extern fns declared under `src/os/` +
`src/lib/nogc_async_mut_noalloc/`" against names matched by
`insert_*!(...)`/`"name" =>` grep produced "543 of 676 unregistered".

**That number is wrong and should not be used.** `rt_string_char_at` was in
that 543 and demonstrably *works* at runtime, so the extraction has false
negatives: extern resolution reaches names through paths the grep did not
model (method-call lowering, aliasing, and other registration forms). The
true unregistered set is some unknown subset of 543 — the real figure needs a
runtime probe (call each name and catch the error), not a grep.

What survives from that exercise is only the qualitative split, which the two
confirmed names illustrate:

1. **Ordinary runtime externs** that merely lack a binding — mechanical to
   register.
2. **Baremetal/hardware externs** (`unsafe_addr_of`, `rt_x86_syscall`,
   `mmio_read*`, `pmm_alloc_page_raw`, `_get_kernel_start`) that a hosted
   interpreter cannot execute at all. These need either a test double
   registered for the hosted lane, or the specs reclassified as QEMU/board
   tests rather than unit tests.

Both confirmed failures are category 2.

## Why not fixed now

- The registry is **Rust seed** code (`src/compiler_rust/…`), outside this
  lane's scope (`src/os/`, `src/lib/nogc_async_mut_noalloc/`) and against the
  standing "Fix .spl not Rust" / "Pure Simple First" rules. There is no
  pure-Simple registry to fix instead — `src/compiler/10.frontend/core/
  interpreter/` mentions these names only in comments. Editing the seed also
  forces a rebuild while other sessions are live in this tree.
- For category 2 the real question is architectural (mock seam vs. reclassify
  the spec), not mechanical, and it should be decided once for the whole
  kernel suite rather than per-symbol.

## Measurement note (read before reproducing)

- **`--no-cache --no-cover-check` are mandatory.** Without them results are
  actively misleading — this report had to be revised because of it.
  Concurrent `simple test` runs rewrite a shared path-scoped manifest, so a
  directory of 100+ specs can print `No test files found … Results: 0 total`
  and **exit 0**, which reads exactly like a clean pass. A missing `@cover`
  annotation separately aborts the run so zero specs execute.
- **Cached runs report stale verdicts.**
  `test/01_unit/lib/alloc/mimalloc_secure_spec.spl` showed `PASS (19 passed)`
  from cache while a `--no-cache` run of the same tree showed
  `15 passed, 4 failed`.
- **Directory runs must be sequential** (`.claude/rules/testing.md` F2).
- Treat any `0 total`, or a result that contradicts an earlier one, as
  **unmeasured** — re-run with both flags before believing either.

Binary identity: `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`
(57MB, built 2026-08-04), which prints the bootstrap-seed banner and delegates
to `src/compiler_rust/target/debug/simple`. Findings attribute to the **seed**
interpreter.
