# Native source authority replay

Runtime qualification is pending. Source checks do not establish a passing
native build or admitted compiler.

Run `test/01_unit/app/compiler_entrypoint/source_authority_spec.spl` with a
refreshed self-hosted test runner. Both integration cases create the same
single-file Hello source under `src/app/cli/bootstrap_main.spl`, initialize and
commit a real Git fixture through SOSIX, and call the shared acquisition and
publication helper. The source content prints `phase2-hello-ok`.

The positional case selects `src/app`, `src/lib`, `src/compiler`, and the entry.
The named case selects `./src/app` and `./src/app/cli/bootstrap_main.spl`.
Both must freeze exactly one identical source file. Event refresh receives
supported src/test families; snapshot selection keeps the original selectors.

The retained producer's failing public native-build replay is recorded at
`/mnt/simple-bootstrap-6b2/phase2-hello-root-250c-20260930/plan.json` and
`compile.log`. Its launcher uses an exclusive claim and must not be rerun in
that evidence directory. Once a refreshed producer is available, use a new
isolated fixture and separate caches to replay the recorded positional route
and the supported named-entry route. Verify the executable exits zero and
prints exactly `phase2-hello-ok`. Preserve the original receipt and cache;
do not inject a digest or disable the authority check.
