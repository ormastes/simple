# Native SPipe spec reports failures but exits zero

Status: open; test gates must inspect the example verdict.

`test/02_integration/compiler/cache/cold_hir_compact_output_index_spec.spl`
reported `4 examples, 4 failures` in a native executable on 2026-09-29,
but the process exited with status 0. A runner that uses only exit status
would accept a failing integration spec. Fix the native SPipe main/exit path
to return nonzero when any example fails, and add a tiny intentionally failing
native spec that asserts both the text verdict and process status.
