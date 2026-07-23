# native-build: missing --output directory → silent worker exit 1

- **Date:** 2026-07-23
- **Severity:** minor (UX) — cost two full ~25-min rebuild cycles to diagnose
- **Repro:** `simple native-build ... --output build/bootstrap/repro/w66` where
  `build/bootstrap/repro/` does not exist (e.g. swept by a parallel `--clean`).
- **Observed:** worker completes the whole pipeline (`[llvm-tools] read-bytes`
  reached), then exits code 1 with **no error message at all** — only the driver's
  generic `error: native-build worker exited with code 1`.
- **Expected:** either `mkdir -p` the output's parent directory before writing,
  or a clear `error: cannot write output '<path>': no such directory`.
- **Fix sketch:** in the native-build worker's final write step
  (`src/app/cli/native_build_worker.spl` output emission), create the parent dir
  or report the write failure with the path and OS error.
