# Linux OCI executable override

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_entrypoint_override_spec.spl`.

Status: **AUTHORED / UNEXECUTED**. No runtime generator or container execution
was used. These are source acceptance scenarios, not passing test results.

1. Constructs exact Podman and Docker argv without interpreting workload values.
2. Preserves build entrypoint then read-only input and writable output mount order.
3. Rejects malformed override through both validate and standalone builder.
4. Rejects an override which the bare runc builder cannot implement.
5. Binds mode changes in either direction before effects and preserves identical replay.
6. Preserves empty leading and trailing workload arguments in the full provider vector.

The checks use actual command-mapping/provider request branches and literal argv
values. No joined command string proves shell safety. Mode replay is checked
against the existing payload binding; executor-entry counts detect refused
attempts even if no scripted command matches. Image ENTRYPOINT inheritance does
not claim complete Kubernetes image-default CMD equivalence.

Runtime validation remains blocked by the unchanged secure-memory producer
failure; no build was retried. See
`doc/05_design/oci_command_entrypoint_admission.md` for provenance and limits.
