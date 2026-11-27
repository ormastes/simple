# native-build: missing --output directory → silent worker exit 1
## Closed 2026-11-25 — fixed in source (see Resolution below)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.
Superseded by the 2026-11-25 resolution section below.

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

## Resolution — 2026-11-25 (closed: fixed in source)

**Root cause.** The worker's native-build funnel
(`cli_native_build_with_environment_variant_policy_v1`,
`src/app/io/_CliCompile/compile_targets.spl`) wrote the final artifact to the
`--output` path without ensuring the parent directory existed and without
reporting the write failure, so a missing `--output` parent surfaced only as a
bare worker exit 1. The driver
(`src/app/cli/native_build_main.spl`) then relayed only its generic
`error: native-build worker exited with code 1`.

**Fix (already landed, commit `c902e5cf555` "native-build mkdir --output
parent (silent exit-1 fix)" plus later hardening).** Both halves of the fix
sketch are in current source:

1. `src/app/io/_CliCompile/compile_targets.spl:1547-1560` — unconditional
   mkdir -p of the output's parent before the pipeline runs
   (`_cli_dir_create_impl(out_parent, true)`, the module's existing
   `dir_create` facade), failing loudly with
   `Error: could not create output directory <parent> for --output <output>`
   if creation itself fails.
2. Every later write step fails loudly with the path named: missing staged
   output (`compile_targets.spl:1914`), functionless artifact
   (`compile_targets.spl:1931`), and publish/rename failure
   (`compile_targets.spl:1942`).
3. The driver now relays the worker's stderr and its last diagnostic line on
   failure (`src/app/cli/native_build_main.spl:3092-3114`), so the worker's
   `Error: could not create output directory ...` reaches the terminal instead
   of the bare generic message.

**Verification evidence and its limits (2026-11-25, Windows host).**

- `test/01_unit/app/cli/native_build_missing_output_fail_closed_spec.spl`
  under the deployed beta.11 binary, interpreter mode: PASS 4/4. This spec
  pins the fail-closed artifact gates at both layers and the in-source
  reference to this bug.
- `test/01_unit/compiler/driver/build_intermediate_path_spec.spl`: PASS 3/3
  (pins `native_build_output_parent` path computation used by the mkdir).
- End-to-end repro (`bin/simple native-build --backend=llvm --entry hello.spl
  -o <missing-parent>/hello`) is **environment-blocked on this host**: the
  deployed v1.0.0-beta.11 Rust seed panics (`=== PANIC ===`, empty message)
  while interpreting the current compiler source, long before the output-write
  step. No execution evidence of the mkdir path itself was obtained; the
  pre-flight mkdir and error paths above are verified by code inspection only.
  The original symptom (silent exit 1 with no message) cannot be produced by
  the current source by inspection: every write failure on the funnel prints a
  path-bearing error and the driver relays worker stderr.

