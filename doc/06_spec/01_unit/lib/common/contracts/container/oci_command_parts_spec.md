# OCI executable and workload argv mapping

Source: `test/01_unit/lib/common/contracts/container/oci_command_parts_spec.spl`.

Status: **AUTHORED / UNEXECUTED**. No runtime generator or container execution
was used. These are source acceptance scenarios, not passing test results.

1. Keeps the executable scalar and preserves literal tail values.
2. Preserves legacy positional command vectors.
3. Keeps image entrypoint selection for empty commands and args-only requests.
4. Rejects a missing override executable.
5. Rejects engine option or JSON interpretation of a selected executable.
6. Rejects NUL in every workload argv position in either mode.

The checks use actual command-mapping/provider request branches and literal argv
values. No joined command string proves shell safety. Mode replay is checked
against the existing payload binding; executor-entry counts detect refused
attempts even if no scripted command matches. Image ENTRYPOINT inheritance does
not claim complete Kubernetes image-default CMD equivalence.

Runtime validation remains blocked by the unchanged secure-memory producer
failure; no build was retried. See
`doc/05_design/oci_command_entrypoint_admission.md` for provenance and limits.
