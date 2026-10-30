# parse_fibers_every_file_errors_2026_10_27 — every parse-fiber file reports an error

- Severity: P1 (phase-3 whole-program bootstrap blocked) — Status: fixed (pending stage redeploy)

## Symptom
Stage2 `C:/dev/p3new/stage2.exe` (sha 6b0ba5f3, release ~824ab2671ba), native-build
whole-program route, log `C:/dev/p3new/buildwp.log`: every `--parse-fibers=i/13` child
printed `files=N parsed=N done=N errors=N` (187/187, 65/65, 89/89, 72/72) and exited 1,
with no reason printed. One shard exited -1073741819 (access violation). The
`--parse-shard` path (`SIMPLE_FILE_FIBERS=0`) on the same binary completed 8/8.

## Root cause
`file_fiber_begin_v1` (`src/compiler/80.driver/driver_build/file_fiber_v1.spl:264`)
built the run with `tldr: texts, error: texts` and `op: zeros, fd: zeros`: one array
value passed to two fields. In compiled code arrays are shared references, so
`parse_done` writing `self.tldr[i] = tldr` also made `self.error[i]` non-empty. So
each file parsed OK (`parsed` += 1) and was then counted as an error whose "message"
is its own TLDR text. Also, `error[producer] != ""` made every importer fail with
"import X failed: <tldr>". The `op`/`fd` alias mixes IO op ids with file descriptors
on the read path (`content == ""`), which is the likely source of the one access
violation. This is unconfirmed: whole-program children pre-read content, so that
path is rarer.

The Rust-seed interpreter copies arrays on field init, so it does not reproduce the
bug. The new spec passes there both before and after the fix. It guards the
invariant for compiled runs.

## Fix
- One fresh array per field in `file_fiber_begin_v1`.
- `_driver_run_parse_fibers` (`driver_parse_shard_entry.spl`) prints the first 5
  `error: parse fiber <path>: <err>` lines to stderr before the summary.
- Spec: `test/01_unit/compiler/driver/file_fiber_v1_spec.spl`, "per-file result
  arrays are distinct (tldr write never sets error)".

## Workaround
`SIMPLE_FILE_FIBERS=0` selects the plain `--parse-shard` route
(`src/app/cli/native_build_main.spl:803`).
