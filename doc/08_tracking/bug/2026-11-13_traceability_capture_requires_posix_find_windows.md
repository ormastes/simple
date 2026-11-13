# traceability config capture requires POSIX `find`, so it cannot run on Windows

Status: confirmed genuine product bug (Windows portability). The
`traceability` CLI exits 2 ("Cannot establish configuration presence") on any
scan, so `traceability_log_modes_spec.spl` cannot pass on a Windows host.

## Evidence

```
mkdir %TEMP%\trace_repro && cd %TEMP%\trace_repro
simple run src/app/traceability/main.spl --log-mode=json .
# exit 2; structural_report_v1 emits
#   TRC-CONFIG-CAPTURE ... "Cannot establish configuration presence"
```

Creating `%TEMP%\trace_repro\.git` does not change the outcome (still exit 2),
so the failure is not "missing repo root".

`src/app/traceability/capture_v1.spl:163` enumerates the configuration root
with `capture_walk_v1(".", ["-maxdepth", "1", "-name", "config"], ...)`. Those
`-maxdepth` / `-name` flags are GNU `find(1)` options; on a native Windows host
there is no GNU `find`, so the walk returns `Err` and line 165 maps it to
`capture_issue_v1("TRC-CONFIG-CAPTURE", "", "Cannot establish configuration
presence", ...)`, forcing `exit_code: 2, qualification: incomplete`.

## Cause and scope

The traceability capture path shells out to POSIX `find` for directory
enumeration instead of using a host-portable directory API. Any Windows run —
including the log-modes spec, which scans an empty fixture workspace — takes
the config-capture error branch. Porting `capture_walk_v1` to a portable
directory walk (or the repo's `dir_list`/facade) is a product change in the
traceability lane, not bounded here.

## Correctness gate for a repair

1. Replace the `find`-based `capture_walk_v1` enumeration with a host-portable
   directory walk and re-validate the maxdepth/name filtering semantics.
2. Confirm the empty-workspace path yields the clean result
   (`traceability: clean`, exit 0) on both Windows and POSIX.
3. Re-run `test/02_integration/app/traceability_log_modes_spec.spl`; the three
   red scenarios (json scan, dot progress, invalid log mode exit code) must
   pass on Windows without regressing POSIX.
