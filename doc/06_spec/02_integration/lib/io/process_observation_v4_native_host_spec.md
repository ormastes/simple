# Process Observation V4 native host lifecycle

Authored companion to
`test/02_integration/lib/io/process_observation_v4_native_host_spec.spl`.

**Status:** Simple-native assertions are pending the qualified compiler run.
The C fixture was built and executed independently in the Linux BuildRunner
container; this is fixture evidence, not a pass for the Simple spec.

## Fixture evidence

Build with:

```sh
sh scripts/check/build-process-observation-v4-static-fixture.shs \
  /work/hal-v4-fixture-20261030/static_child
```

The script requires a static Linux `ET_EXEC` ELF without `PT_INTERP` and prints
its SHA-256. The recorded artifact was ELF64 little-endian AArch64 with digest
`aafb9a0e1858795c98893a88e4217effcef91db6d0465902ed3106441b1ddebd`. Direct
execution returned exit 23, stdout `native-v4\n` (hex
`6e61746976652d76340a`), and empty stderr.

## Simple-native assertion

Set `PROCESS_OBSERVATION_V4_STATIC_FIXTURE` to the built artifact, then run the
spec with the qualified Linux native backend. It pins the executable and cwd,
starts a real leader-only child through the public V4 facade, collects and
freezes the actual receipt, and acknowledges that exact snapshot. Assertions
cover exit status 23, exact stream bytes, leader reaping, Ack packet identity
and binding, and retired lease state.

This scenario exercises `LeaderOnly`; it does not qualify process-group
containment, descendant cleanup, or a process-tree-empty guarantee. Group
ownership remains a separate unqualified contract.

The exceptional `CleanupPending` fixture, wrong-digest cleanup refusal, and
child/descriptor leak oracle remain `MissingEvidence` in
`process_observation_cleanup_v4_spec.md`; this case does not qualify them.
