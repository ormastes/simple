# Windows redirected parallel process qualification

Requirement coverage: REQ-WIN-PAR-001 through REQ-WIN-PAR-006.

The operator builds the native fixture and owner probe with the selected admitted producer/runtime, then selects an executable path containing spaces/Unicode and a new private probe directory. The actual probe launches80 owned children behind a barrier twice, records native exit codes and stream/environment isolation, then exercises lifetime and failure cleanup. It reports Results and peak RSS; the SSpec wrapper requires positive evidence instead of passing on absent artifacts.

Executable specification: test/02_integration/lib/windows_parallel_process_owner_spec.spl.
Probe: test/02_integration/lib/windows_parallel_process_owner_probe.spl.
Fixture: test/fixtures/runner/windows_parallel_child.spl.

Evidence status: NOT RUN. Native producer and cross-platform target qualification are required before marking this manual PASS.