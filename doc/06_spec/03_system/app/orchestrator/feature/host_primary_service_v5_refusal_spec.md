# V5 primary-service command refusal

**Status: AUTHORED_NOT_RUN.** Manual authored from the executable SSpec; docgen
was not run. Evidence class: command-boundary, not a live Windows system test.

Executable: `test/03_system/app/orchestrator/feature/host_primary_service_v5_refusal_spec.spl`.
Requirements: HOST-01 (host admission), CTR-02 (typed execution boundary).

The first five scenarios invoke the actual `host_primary_service_command_v5`
with invalid arguments and assert exit code 2, the exact canonical refusal
reply, and no retained recovery owner. A prior shape assertion prevents this
fixture-free suite from accidentally starting a valid service. The sixth
scenario calls only the public shape validator; its success proves no
enrollment, filesystem identity, capacity grant or readiness.

| Scenario | Steps and expected result |
| --- | --- |
| Command shape | Submit missing, extra and wrong command arguments; require `host-primary-service-usage`. |
| Backend selection | Submit an unknown backend; require `host-service-backend`. Select Linux with its valid dash fields; require the current direct-connection unsupported error. Existing Linux V4 service behavior is outside this suite. |
| Installed fields | Remove the anchor, policy pin or binding file; require the matching installed-field error. |
| Endpoint | Submit public, fixed-port, hostname, IPv6, alternate numeric and NUL spellings; require `host-primary-service-loopback-auto-required`. |
| Credential | Submit empty and NUL-bearing paths; require `host-primary-service-credential-required`. |
| Syntax versus authority | Validate syntactically complete arguments with unverified paths; do not invoke startup or claim those paths are admitted. |

These assertions do not instrument OS call counts and cannot prove native
absence after an admitted effect. Real credential publication, authenticated
connections, Docker execution, attach, resize, cancellation, crash recovery and
capacity settlement remain covered only by their separately pending acceptance
work. This spec requires the integrated V5 app, Host and smux source closure;
those files currently span the active implementation worktrees.
