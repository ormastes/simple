# Stage 2 Native SSpec Runner Process Crash

## Status

OPEN. Do not run a full bootstrap until the bounded Stage-2-only runner recipe
below is tried.

## Evidence

The admitted Retry 15 Stage 2 pure-Simple compiler can native-build
`rv32_nvme_nand_read_level_spec.spl` in 10.85 seconds. The resulting 35,120-byte
x86-64 executable reaches `rt_process_run` and then terminates with SIGSEGV in
`memcpy` before producing an SSpec summary. An unstripped rebuild gives the same
backtrace:

```text
__memcpy_avx_unaligned_erms
rt_process_run
<generated native spec>
```

The broad `src/app/test_runner_new/main.spl` build without an explicit runtime
bundle fails after 52.72 seconds in nine transitive debug/signal/coverage
modules. These are runner-closure failures, not NVMe firmware failures.

Evidence:

- `build/logs/stage2-nvme-sspec-direct/`
- `build/logs/stage2-sspec-runner/`

## Next Bounded Attempt

Build the existing runner with the corrected Stage 2 runtime authority:

```sh
SIMPLE_LIB=src \
SIMPLE_RUNTIME_PATH=build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority \
SIMPLE_NO_STUB_FALLBACK=1 \
build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple \
  native-build --target x86_64-unknown-linux-gnu --backend llvm \
  --runtime-bundle core-c-bootstrap \
  --runtime-path build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/test_runner_new/main.spl \
  --mode one-binary --strip \
  --output build/bootstrap/stage2-tools/simple_test_runner
```

Run the NVMe spec with `--fork --mode=interpreter --no-session-daemon
--sequential --no-cache --no-db`; fork mode uses `rt_cli_run_file` instead of
spawning the unavailable Stage 2 `run` command. Build
`src/app/spipe_docgen/main.spl` separately with the same runtime authority.

Stop after one build/run attempt. If it still fails, resume Stage 3 only with
the existing 90-minute cap; do not start a full bootstrap.
