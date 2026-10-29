# Native test-runner capture limit has private declaration visibility

The source-matched native SSpec runner passes HIR/MIR for all 304 modules, but
Cranelift rejects nine importing modules because `TEST_OUTPUT_CAPTURE_BYTES`
is a non-public module static. The defining `test_runner_types.spl` declares
it with `val`, although the package facade explicitly exports it and runner,
doctest, process-tracker, and lifecycle modules import it directly.

Declare this existing shared constant `pub val` in its defining module. Keep
its 4 MiB value and the backend's private-static rejection unchanged. This
restores the intended cross-module API without making unrelated statics public.

Native failure evidence:
`/work/buildrunner-pair-6304-20261030/sspec-runner-9g/logs/build.log`.
The run completed below its 9.5 GiB process-tree limit: 295 native units passed,
nine failed, and link/publication was refused. No runner image was produced.
Producer SHA256:
`6304c166acbcac0a1ea78534fc9a5859507a87ad655eabf98618c798045ad6e8`.

Focused native regression:
`test/fixtures/test_runner/native_output_capture_limit.spl` imports the shared
scalar from another module and requires its exact value before printing a
success marker. Its native red/green validation and the full runner rebuild
are pending. This record does not claim native SSpec or HAL/SOSIX execution.
