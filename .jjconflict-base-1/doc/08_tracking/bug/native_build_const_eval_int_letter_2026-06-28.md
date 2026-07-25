# native-build const-eval: hex-letter parse (FIXED) + residual typed/module-val gaps (OPEN)

Date: 2026-06-28

Lane: `.spipe/simpleos-alpine-harden-musl-busybox` (AC-6b — cross-compile simplebox)

## Part 1 — hex literal with an a-f digit fails const-eval — **FIXED 2026-06-28**

`native-build` aborted with `error: semantic: cannot parse 'c' as i64` (seed
`interpreter_call/builtins.rs:613`) when const-evaluating **any hex literal
containing a letter digit a-f / A-F**. The parser
(`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl`) mapped hex
digits with `int(hc) - int("a") + 10`; the `int()` builtin numeric-parses, so
`int("a")`/`int("c")` errored. The error letter was the first hex letter
encountered (`0xc...` → `'c'`, `0x7f...` → `'f'`).

Minimal repro (now passes):
```
val MAGIC: u64 = 0xc5e77b6b397e7b43   # was: cannot parse 'c' as i64
```

Fix: map hex digits via a lookup string (same idiom as
`lexer_struct.spl:lex_escape_hex_value`), no `int(<letter>)`. Verified:
`0xca=202`, `0xff=255`, `0xDEAD=57005`, `0xAbCdEf=11259375`, `0x10=16`, binary
`0b1010=10`, octal `0o17=15`. Regression guard:
`test/01_unit/compiler/hex_literal_const_eval_spec.spl` (7/0).

This is why the kernel `0xc...` LIMINE constants (scanned by `--source src/os`)
tripped the simplebox build. Pre-existing; unrelated to this lane's libc port
(proven by a marker test: renaming the lane's `["c", ...]` library list to
`["zzcmark", ...]` left the identical `'c'` error).

## Part 2 — native-build worker timeout (lever a) + entry-closure scoping (lever b) — **FIXED 2026-06-28**

With Part 1 fixed, the **real** simplebox build (the committed invocation:
`--backend llvm --source src/os [--source src/lib] --entry
simplebox_main.spl --entry-closure --target x86_64-unknown-none --linker-script
…/simpleos.ld`) now progresses past parsing and dies with:

```
[TIMEOUT: Process killed after 120s]
BUILD_EXIT=255
```

This message is Simple's own `process_run_timeout` (`process_ops.spl`, 120s
default) — native-build shells out to a sub-step (it holds a `bin/simple` path;
`NativeProjectBuilder::new(project, ".../bin/simple")`) bounded at 120s. The
freestanding build of simplebox discovers/parses the `src/os` tree (**1241
`.spl` files**) and exceeds 120s before emitting. Reproduces with `--source
src/os` alone (no `src/lib`), and the run had no external `timeout`/`process.run`
wrapper — so the 120s is internal to native-build, not the harness.

NOTE: the earlier "Part 2" claim here (typed/module `val` → "unwrap on Type" /
"kind on nil") was measured from **barebones 3-line files** built without
`--target`/`--source`/`--linker-script`. That is the wrong invocation and is
contradicted by `simpleos_stdlib_num.spl` (which has an in-function typed `val`
and `0x7fffffff`) compiling to a real freestanding ELF. Minimal repros mislead
for native-build — the real-unit result above supersedes them.

Root cause (traced via `ps`): native-build delegates to a worker subprocess
`timeout 120 bin/simple run src/app/cli/native_build_worker.spl …`
(`native_build_main.spl:70`), hardcoded to **120s**, which killed the worker
mid-compile.

- Lever (a) — **FIXED**: `native_build_main.spl` now honors `--timeout <secs>`
  and defaults to **1800s** (`native_build_timeout_ms`). Verified live: the
  worker wrapper shows `timeout 1800` and the build runs well past 120s without
  being killed.
- Lever (b) — **FIXED 2026-06-28** (discovery scoping): the pure-Simple worker
  path (`cli_native_build` → `CompilerDriver`) never implemented `--entry-closure`
  — it was mis-parsed as `--entry` (eating the next token), and the driver
  bulk-loaded all of `src/{app,lib,compiler,runtime}` plus every file in each
  `--source` dir, so a simplebox build parsed ~1241 `src/os` files (+ the whole
  compiler) and could never emit (multiple `main`s → undefined `__simple_main`).
  Now, gated entirely on `--entry-closure` (previously a no-op → no regression):
  parse it as its own flag; BFS the entry's import closure (FS-resolve each `use`,
  mirroring the Rust discovery fallback incl. leading-dir-name strip) and compile
  only those files; export `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE` so `driver.spl`
  skips its implicit whole-src bulk-load (default path byte-identical → bootstrap
  unaffected). **Verified: simplebox closure loads exactly 3 files**
  (`simplebox_main` + `simplebox_dispatch` + `simpleos_stdlib_num`) vs 1241, and
  the entry's `main` resolves. Landed `src/app/io/_CliCompile/compile_targets.spl`
  + `src/compiler/80.driver/driver.spl`.
  - Residual (separate): the worker still runs on the **stale** `bin/simple`
    *interpreter*, so codegen of even 3 files is minutes-slow. Deploy a fresh
    self-hosted binary to the worker path to make it fast. Also: this Simple
    path ignores `--target`/`--linker-script`, so it emits a host (not
    freestanding) binary — a separate gap from discovery scoping.

## Earlier mis-diagnoses (corrected)

The first version of this bug claimed "exit 255, no binary, no error / no emit
for multi-module freestanding entries." That conflated three unrelated things,
none of which is a cross-module emit gap:
1. **120s death** = Simple's own `process_run_timeout` 120s default
   (`process_ops.spl:77`) in the *test harness* — not native-build.
2. **`ld.lld: cannot open simple_rt_runtime.o`** = the **stale deployed**
   `bin/simple` seed; the current cargo seed does not have this error.
3. **The real wall** = the hex const-eval bug above (Part 1), now fixed,
   revealing the typed/module-val gaps (Part 2).

A single pure-Simple libc module (`simpleos_stdlib_num.spl`) compiles to a real
freestanding PIE ELF with the current cargo seed — the libc port is sound.

## Acceptance for closure (Part 2)

- `native-build` emits a real freestanding ELF for a typed-`val` program and for
  `simplebox_main.spl` (`--source src/os --entry-closure --target
  x86_64-unknown-none`), linked against the SimpleOS sysroot.
- Then `build_simplebox("x86_64-unknown-none")` produces a runnable
  `build/os/rootfs/bin/simplebox` and `simplebox seq '  2'` proves
  `libc_strtoul` executes in the compiled binary.
