# SimpleOS WM harness: multi-hour kernel build is fully silent — misdiagnosed repeatedly as hang/crash

- **Date:** 2026-07-26
- **Lane:** `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`, macOS host
- **Status:** root-caused (read-only analysis); zero-code-change mitigation identified; small fix set described

## Symptom
During harness runs 3-8, both the harness stdout log and `$BUILD_DIR/native-build.out`
stay **0 bytes for the entire 2h+ kernel cranelift build**. Operators misdiagnosed the
silence as a hang or the nil-receiver crash at least twice
(`native_build_nil_receiver_crash_2026-07-25.md`), burning multiple 2700-7200s runs.

## Root cause (three stacked, none of them `--log off`)
1. **`--log off` is orthogonal.** It parses into `log_mode`
   (`src/app/io/_CliCompile/compile_targets.spl:111-117`) and is exported as
   `SIMPLE_OS_LOG_MODE`, which only decides whether the **compiled guest kernel**
   carries runtime serial-logging code. It adds/removes zero lines of build progress.
2. **The harness never enables the progress gates that already exist.** Per-module
   heartbeat `[NATIVE] compiling module: {name}`
   (`src/compiler/80.driver/driver_aot_output.spl:928`) and per-phase
   `[BOOTSTRAP-PHASE] +{elapsed_ms}ms ...` (`driver_log_helpers.spl:44-46`, 63 call
   sites) are gated behind `SIMPLE_COMPILER_TRACE=1` /
   `SIMPLE_COMPILER_PHASE_PROFILE=1`, which the harness does not set. No stage-start
   echoes exist in the harness either; its only output primitive is `emit_failure()`.
3. **stdout is never flushed per line.** `print` → `spl_print` → `fputs(stdout)` with
   no flush (`src/runtime/runtime.c:932-934`); under a file redirect libc
   fully-buffers, so even trace-enabled module lines lag by KBs.
   `eprint` (phase heartbeat) is effectively unbuffered and would appear live today.

## Zero-code-change mitigation (use in the next harness run)
Add to the native-build env prefix (harness `:603-605`):
`SIMPLE_COMPILER_TRACE=1` (or lighter `SIMPLE_COMPILER_PHASE_PROFILE=1`).
Optionally `--verbose` for driver start/finish lines. The stderr-side
`[BOOTSTRAP-PHASE]` lines appear live in the merged redirect.

## Minimal fix set (described, not yet applied)
- **Harness:** one-line stage-start echo with UTC timestamp before each major stage;
  optionally a background byte-count poller for `native-build.out`.
- **Compiler:** call the existing `rt_stdout_flush()` (`runtime_native.c:1575`) after
  each `[NATIVE] compiling module:` print so trace output is live under redirects.
- Both conform to the log-retention policy (level/env-gated, off by default).

## Landmine noted
The alternate `native_build_main.spl` double-subprocess dispatch path buffers the
child's entire output in a temp file and only prints after exit
(`process_ops.spl:83-130`, `native_build_main.spl:231-233`) — if a long build ever
routes through it, the same total-silence symptom returns with a different cause.
