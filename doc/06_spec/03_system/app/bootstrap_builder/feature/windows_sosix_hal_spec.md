# Windows BuildRunner native SOSIX process path

Executable specification: `test/03_system/app/bootstrap_builder/feature/windows_sosix_hal_spec.spl`.
Native probe source: `test/fixtures/bootstrap_builder/windows_sosix_hal_probe.spl`.

The test requires a Windows native runtime, a real compiled Windows worker,
a separately compiled probe from the source above, and an existing private
directory. Set `SIMPLE_BUILDRUNNER_WINDOWS_WORKER`,
`SIMPLE_BUILDRUNNER_HAL_PROBE`, and `SIMPLE_BUILDRUNNER_HAL_ROOT` to their
absolute paths. Missing executables or root fail with `MissingEvidence` on
Windows. Other hosts report the case as pending.

The probe stages an input through the real manager transport, launches the
real worker and a real `cmd.exe` child, and checks the output, stdout, stderr,
process exit, Job Object memory receipt, capacity settlement, and child-tree
reap evidence. The specification independently reads the result and evidence
files and verifies the output digest. No mocked process port is used.
The producer is `cmd.exe` writing a fixture artifact; this checks real process
ownership and transport, not compilation of a Simple program.

This manual describes the expected test; it is not a record of a live pass.
