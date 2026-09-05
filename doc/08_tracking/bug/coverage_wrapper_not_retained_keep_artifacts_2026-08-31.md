# A failing coverage/MC-DC wrapper cannot be captured for inspection

Date: 2026-08-31
Status: OPEN
Impact: has blocked **three** separate investigations in one day.

## The gap

`build_coverage_wrapper` (`src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`)
and the `spipe_*` native-entry builder
(`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:893`) write generated
sources into `_tp_get_temp_dir()` and the runner then deletes them via
`cleanup_native_generated_files`. When one of those generated files fails to
compile, the error text names only the generated path — and by the time anyone
reads it, the file is gone.

`--keep-artifacts` (`test_runner_args.spl:323`) did **not** preserve one in
practice: two runs with `--keep-artifacts` (one also with `--force-rebuild`) left
no `spipe_wrapped__*` or `simple_cov_*` file for either spec. Whether that is a
plumbing bug in the flag or a path where cleanup runs regardless has not been
traced; either way the flag does not currently deliver the artifact.

## Why it matters

The compile error names the ROOT compile unit, never the module the bad
identifier is in:

```
error: compile failed (/mnt/data/tmp/spipe_wrapped__..._spec_native.spl):
  semantic: ...: Undefined("undefined identifier: io_runtime")
```

So the only way to locate a failure is to reconstruct the closure by hand with
probe files. That works, but it answers a *different question* — a probe's
closure is not the wrapper's — and it is exactly how a wrong root cause got
written up and had to be retracted (see
`coverage_wrapper_undefined_identifier_clusters_2026-08-31.md`, cause A). Roughly
20 symbols in that document sit in cause F, unlocatable, purely because no
wrapper can be captured.

## Two things worth fixing

1. **Retain on failure, unconditionally.** A generated source that failed to
   compile should never be deleted, `--keep-artifacts` or not. The artifact is
   the only evidence of the failure and it costs one file.
2. **Name the artifact in the diagnostic, and isolate it per run.** Wrappers are
   written to a shared temp dir (`/mnt/data/tmp` here) under spec-derived names
   with no per-run scoping; wrappers from other concurrent sessions were observed
   appearing there mid-investigation. A per-run subdirectory would make captures
   attributable and rule out cross-run interference — currently listed as an
   unexcluded hypothesis in cause F.

## Suggested acceptance check

A spec whose wrapper fails to compile leaves exactly one readable generated
source on disk, whose path is printed in the error, and
`bin/simple compile <that path>` reproduces the same diagnostic standalone.
