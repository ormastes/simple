# CI container executable mapping

Source: `test/02_integration/app/ci/container_command_mapping_spec.spl`.

Status: **AUTHORED / UNEXECUTED**. No runtime generator or container execution
was used. These are source acceptance scenarios, not passing test results.

1. Maps a nonempty command to executable override with exact literal workload argv.
2. Keeps the image entrypoint when command and args are absent.
3. Keeps args-only values after the image without manufacturing an executable.

The checks use actual command-mapping/provider request branches and literal argv
values. No joined command string proves shell safety. Mode replay is checked
against the existing payload binding; executor-entry counts detect refused
attempts even if no scripted command matches. Image ENTRYPOINT inheritance does
not claim complete Kubernetes image-default CMD equivalence.

Runtime validation remains blocked by the unchanged secure-memory producer
failure; no build was retried. See
`doc/05_design/oci_command_entrypoint_admission.md` for provenance and limits.
