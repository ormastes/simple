# Interpreter: method-call result passed directly as a method argument is corrupted (nested subprocess) - 2026-06-30

## Status

Open. Worked around in the NVMe firmware by binding the inner call result to a local `val`
first (`ftl_gc.spl` selftest, `nand_migration_capture_main.spl`).

## Summary

When a **method** call's return value is passed *directly* as an argument to another method —
`outer.m(inner.n(...))` — the inner value is corrupted at the call boundary, so the outer
method receives a wrong value. The corruption is **context-dependent**: the program runs
correctly under `bin/simple run` directly, but fails when the same program runs as a
**subprocess of the interpreter** (e.g. an sspec/`bin/simple test` `process_run` child) — and
in that nested context it is **deterministic**, not flaky.

Passing a **free-function** result as an argument (`fw.submit(cmd_make(...))`,
`aq.cq_post(cpl_make(...))`) is **not** affected — that idiom is used throughout the firmware
and its e2e tests pass. Only a **method**-call result as an argument triggers it.

## Reproduction

```simple
val p: i64 = band.alloc_page()      # WORKS: bind first, then pass
band.mark_valid(p)

band.mark_valid(band.alloc_page())  # CORRUPTS under a nested interpreter:
                                    # mark_valid receives a wrong ppn, the block is not
                                    # marked valid, and a later wear-victim scan reads UNMAP
```

Observed: `examples/09_embedded/simpleos_nvme_fw/fw/ftl_gc.spl`'s `ftl_gc_selftest` used
`band.mark_valid(band.alloc_page())`. Standalone (`bin/simple run test_fw.spl`) it passed
8/8; run as the system spec's `process_run("/bin/sh", ["-c", "bin/simple run test_fw.spl"])`
child it consistently failed exactly one assertion ("coldest closed block is the wear victim
-- expected 0 got -1") because the blocks were never marked valid. The aggregate self-test
reported `FIRMWARE TESTS FAIL (1)` only in the nested context.

## Mitigation

Bind the inner method result to a local `val` before passing it:

```simple
val ppn: i64 = ftl.physical_ppn(100)
val word: i64 = ftl.nand_word(ppn)        # not ftl.nand_word(ftl.physical_ppn(100))
```

The firmware's `CONVENTIONS.md` records this alongside the other call-boundary discipline.

## Distinct from existing call-boundary bugs

- `f64_self_hosted_call_result_codegen` — f64-specific (this is integer).
- `array .get(index>=1)` corruption — index-value-specific (this is any method-call result).
- `interp_me_method_first_param_times8_conditional` — corrupts a multi-param `me` method's
  *first parameter* on entry (this corrupts the *argument expression's value* at the call site,
  only for a method-call argument, and only under a nested interpreter).

## Impact

- Test/selftest code using `obj.m(other.method(...))` can fail only when run nested under the
  test runner while passing standalone — easy to miss (the file-level verdict can still read
  PASS). Core firmware service paths use the free-function idiom and are unaffected.

## Verification (2026-07-17)

Runtime attempt at tip 9feac6ef6e5: **CANNOT-REPRO-AS-DOCUMENTED** (with environmental
caveats).

Probes:
- `probe06_inner.spl`: class `Ctr` with `fn next_id()` / `fn mark(x)` (forced through
  interpreter via `me`-vs-`fn` rejection to guarantee interpreter execution)
- `probe06_outer.spl`: spawns `probe06_inner.spl` as OS subprocess via `extern fn
  rt_process_run` (mirroring the doc's "subprocess of the interpreter" scenario)

**Standalone (`bin/simple run probe06_inner.spl`):** correct output `bound_first last=1`,
`inline_arg last=2`.

**Nested subprocess (`bin/simple run probe06_outer.spl` spawns `bin/simple run
probe06_inner.spl` as child):** identical correct output `bound_first last=1`,
`inline_arg last=2` — **no corruption observed**.

**Caveats:**
1. `use std.process.{process_run}` (the doc's own documented API) crashes outright with
   "runtime error: field access on nil receiver" followed by Illegal Instruction,
   even for trivial `/bin/echo` command outside any class/method context
   (`probe06_debug_procrun.spl`). Had to substitute raw `extern fn rt_process_run`
   primitive (confirmed working, `probe06_debug_rawproc.spl`) to build a nested-process
   probe. This std.process wrapper crash is a **separate, distinct, likely
   environment-dependent finding** worth filing separately (see new bug #3 below).

2. `bin/simple test` is itself non-functional at this tip ("error: semantic: unknown
   extern function: rt_cli_arg_count"), so the exact documented trigger path (an sspec
   spawning a `process_run` child via test runner) could not be exercised. Only a
   structurally-equivalent bare nested-subprocess-of-interpreter was tested.

**Status:** CANNOT-REPRO-AS-DOCUMENTED (cannot exercise exact trigger path; bare
nested subprocess shows no corruption).
