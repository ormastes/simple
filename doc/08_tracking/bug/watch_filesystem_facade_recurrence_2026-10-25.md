# Watch filesystem facade recurrence

Status: source repaired; authoritative runtime regression UNRUN.

Frozen revision `46772223a7c`, producer `991be8f97493426d22fa944bd212afa22487bb22b31d2a6ea0ab95e8b4e05974`,
module diagnostics attempt `3cx5IX`, row 18 (`ffi_usage`) failed first-pass HIR
at `watcher.spl:42:12` (`rt_file_exists`) and `:45:17` (`rt_dir_walk`).
Evidence: `module-diagnostics/attempt.3cx5IX/18/module_compile_object.log`,
lines 10629–10630 in the retained Phase3 campaign.

The watcher already imports `file_exists` and `dir_walk` from `std.io_runtime`,
but these two call sites used undeclared runtime names. Restore the exact
call-site repair from `73789ebee823c2eb592b953dcc94536113f26c94` (also present
in donor `c9d0bf532b60ebd4a2c024e36d142449878e2714`). Both facades retain the
same argument/result shape. The independently declared modification-time
runtime boundary remains unchanged.

Restore the donor's `test/01_unit/app/watch/watch_filesystem_facade_spec.spl`:
it covers existing/missing source paths and existing/missing snapshot directories,
including positive modification timestamps. The available admitted compiler is
compiler-only; no qualified test CLI/runner is available. No replacement runner,
Rust seed fallback, live snapshot mutation, or dependency-closure build is used.
