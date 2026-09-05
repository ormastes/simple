<!-- codex-design -->
# Native-build environment timeout detail design

`ConfigEnv` exposes a scoped-key normalizer and typed positive-seconds resolver returning `{ value, source, key }`. Native-build calls it with scope `native-build` and explicit option `timeout-seconds`; verbose output prints `Timeout: <n>s (<source> <key>)`.

The launcher resolves `SIMPLE_NATIVE_BUILD_WORKER_TIMEOUT_SECONDS` separately and prints the effective worker timeout in its launch receipt. CLI remains highest priority where a CLI option exists. An invalid scoped value returns a diagnostic before spawning a worker or compiler.

`ArgParser` derives `SIMPLE_<NORMALIZED_PROGRAM>_<NORMALIZED_OPTION>` and offers an explicit environment-key override for option owners whose semantic unit is not represented in the CLI spelling.
