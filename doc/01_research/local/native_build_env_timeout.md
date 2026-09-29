<!-- codex-design -->
# Native-build environment timeout — local research

The Rust driver and self-hosted `native_all` both feed `NativeBuildConfig.file_timeout`, whose safe default is 300 seconds. The self-hosted facade had drifted to 60 seconds, causing two valid large MIR files to fail at exactly 60 seconds during Stage3. The Pure-Simple `native_build_main.spl` has a separate 7200-second whole-worker timeout; passing `--timeout 300` to it would incorrectly shorten that outer limit.

`simple_common::ConfigEnv` already provides shared argument/environment access for both Rust CLI owners. `std.cli.ArgParser` is the shared Pure-Simple parser and needs the same scoped-name derivation, without an unrestricted environment scan.

## Chosen contract

- Per-file native compiler watchdog: `SIMPLE_NATIVE_BUILD_TIMEOUT_SECONDS`.
- Interpreted whole-worker watchdog: `SIMPLE_NATIVE_BUILD_WORKER_TIMEOUT_SECONDS`.
- CLI explicit value > scoped environment value > declared default.
- Invalid or zero scoped values are diagnostics with a nonzero result; no silent fallback.
- Automatic names use `SIMPLE_<PROGRAM_OR_MODULE>_<OPTION>`, uppercase with non-alphanumeric runs normalized to one `_`; owners may declare an explicit key when units are needed.
