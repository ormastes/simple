# Single-entry TLDR compilation fixture

Prepare `dependency.spl`'s validated interface and object outside the timed
interval. Compile only `main.spl` to an object using that interface, then link
against the previously built dependency and run; the expected exit code is 0.

The measurement must report one entry codegen module and zero imported source
body parses/codegen tasks, including background descendants. Header preparation,
dependency compilation, linking, execution, and artifact-cache hits are separate
results. An entry-closure build does not satisfy this measurement.

Required performance: less than 0.1 seconds for the entry compilation with
prepared TLDR headers. Report invocation wall time as well as internal compiler
phase time; do not hide startup or admission overhead in a faster phase-only
number. Disable reuse of the entry object while retaining valid dependency
interfaces, and report each sample, median, p95, and peak process-tree memory.
Meeting this target does not relax the correctness or invalidation controls.

Correctness controls must invalidate a stale interface after a signature change
and reject an incompatible call. A dependency implementation change must use its
new object for the separate link/run check. Retain source, interface, compiler,
target/options and object identities in the measurement evidence.

Status: fixture prepared; header-only compilation and timing are not yet verified.
