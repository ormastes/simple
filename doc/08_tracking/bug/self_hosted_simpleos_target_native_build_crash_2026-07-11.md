# Self-hosted SimpleOS target native-build crash

Date: 2026-07-11  
Status: Open  
Severity: P0 — blocks target-native `/usr/bin/simple` payload

## Reproduction

```sh
release/x86_64-unknown-linux-gnu/simple native-build \
  --source examples/01_getting_started \
  --entry examples/01_getting_started/hello_native.spl \
  --backend=cranelift --target x86_64-unknown-simpleos \
  -o build/tmp/simpleos-target-probe
```

Current result: exit 1, `timeout: the monitored command dumped core`, no output.
The deployed `bin/simple` is byte-identical to the Rust release seed and cannot
be used as production evidence. The older self-hosted release recognizes the
native-build command but does not advertise `--target`; current source does
parse the flag in `src/app/io/_CliCompile/compile_targets.spl`.

Three cache-isolated recovery probes using both
`release/x86_64-unknown-linux-gnu/simple` and
`build/bootstrap/full/x86_64-unknown-linux-gnu/simple` exited 1 before writing
any cache file or diagnostic, including a single-thread run with
`SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_COMPILER_TRACE=1 --verbose`. A focused
`check src/app/cli/native_build_main.spl` also dumped core. Per the iteration
guard, do not repeat these commands; the next step is native crash/backtrace
diagnosis or a known-good self-hosted redeploy, not another retry.

## Required result

A cache-preserving self-hosted rebuild must produce a static
`x86_64-unknown-simpleos` ELF for the full `src/app/cli/main.spl` entry closure,
after which
`scripts/os/simpleos-native-build.shs` stages it at
`bin/release/x86_64-unknown-simpleos/simple` without using the Rust seed.

## Verification

Run the target-native hello probe first, then the full bootstrap CLI entry with
the same cache. Require static ELF identity and a non-crashing `--version` run;
host-only or seed-built output does not close this bug.

## Pure-Simple runtime archive blocker

A fresh stage2 compiler now advertises `--emit-archive`, but building the
existing `src/runtime/simple_core` archive skips `core_string.spl` after LLVM
verification fails:

```text
Call parameter type does not match function signature
i64 %call50 = call i64 @rt_enum_new(i64 ..., i64 ..., i64 ...)
```

The production Pure-Simple LLVM declaration sites intentionally use
`rt_enum_new(i64,i64,i64)` because MIR operands are widened. The bootstrap Rust
registry still fixes the same symbol to `[I32,I32,I64]`; changing only the
Simple definition or adding `as i32` casts did not survive MIR lowering. Three
bounded attempts reached the iteration cap, so no further archive build was
run. The partial archive was deleted and must not be used as target runtime
evidence. The Rust registry file is concurrently dirty in another session, so
this lane did not absorb or overwrite that work.

After the enum ABI owner is reconciled across both codegens, rebuild only the
failed Simple-core archive once and require the log to contain zero
`FAILED FILES`; exit code zero alone is insufficient.
