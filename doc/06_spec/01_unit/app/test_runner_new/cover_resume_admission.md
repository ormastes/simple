# Coverage admission and checkpoint resume

Status: AUTHORED_UNRUN; manual companion, not generated execution evidence.

Executable unit spec: test/01_unit/app/test_runner_new/cover_admission_spec.spl
Real runner fixture: test/fixtures/test_runner/cover_resume_admission/main.spl

New unit scenarios preserve checkpoint provenance on an empty rejection set,
and preserve checkpoint counters while retaining a named rejected-file failure.
The isolated fixture calls actual run_tests, discovery, cover validation and
checkpoint read/write. It verifies mixed rejection fails, clean resume passes,
and strict mode fails before consuming the checkpoint. Child bodies deliberately
fail so unexpected execution cannot masquerade as success.

Run only from a fresh scratch working directory containing marker
cover-resume-isolated-root, using an admitted runtime and repository library
closure. Never use the repository working directory or an existing checkpoint.
No executed-case count, runtime PASS or coverage percentage is claimed.
