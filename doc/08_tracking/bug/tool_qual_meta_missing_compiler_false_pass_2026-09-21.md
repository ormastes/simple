# Tool qualification reports PASS when its compiler cannot run

**Priority:** P1
**Status:** FIXED (2026-09-21)
**Host:** macOS arm64; affected on every host when the compiler fails

`scripts/check/cert/tool-qual-meta.shs` defaulted to a hardcoded Linux home
directory. On macOS that executable was absent. The runner discarded every
execution's nonzero exit status, compared empty stdout streams, and returned
`RESULT: PASS` for both interpret and compiled modes. The self-test could also
accept missing executions as its deterministic control.

The default now resolves to the checkout's `bin/simple`. Every corpus execution
must succeed before its stdout participates in qualification. Failed first or
subsequent executions produce an execution error naming the mode, run number,
and exit status. Successful empty stdout is still valid. Identity-leak probes
in the self-test also require successful executions.

Validation: `sh test/00_unit/scripts/tool_qual_meta_execution_spec.shs` reproduces
the original missing-compiler false PASS before the fix. After the fix its ten
checks cover the checkout-local default, empty successful output, first and
later failures, failure only in compiled mode, real stdout variation, and
self-test acceptance/rejection. The later and compiled failure fixtures emit
the same stdout as successful runs, so their exit status is decisive.

No compiler bootstrap or real compiler corpus qualification was performed;
these tests qualify the shell runner's handling of executable outcomes.
