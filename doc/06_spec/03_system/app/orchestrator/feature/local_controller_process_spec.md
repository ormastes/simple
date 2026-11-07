# Separate-process metadata controller

Source: `test/03_system/app/orchestrator/feature/local_controller_process_spec.spl`.
Status: **NOT_RUN**. Authored manual, not generated execution evidence.

Each metadata command invokes an actual compiled orchestrator child with bounded timeout/output. Verify immutable UID/sourceDigest, changed-content refusal, policy close/reopen, sticky cancellation and unobserved runtime. No in-process command adapter is used.

The compiled CLI path or fixture must exist before executing the test. No build,
admitted SSpec, compiler qualification, provider execution or authentication PASS
is claimed. Missing executable/fixture produces real assertion failure.
