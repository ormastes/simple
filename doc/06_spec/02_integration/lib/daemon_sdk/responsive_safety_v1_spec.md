# Public SDK readiness callback safety

Status: **AUTHORED_NOT_RUN**. Executable:
`test/02_integration/lib/daemon_sdk/responsive_safety_v1_spec.spl`.
Requirements: DAE-02 partial, REQ-DAE02-SDK-SAFETY-001–004.

Each scenario calls the actual production helper, using its existing callback
contract and a unique private temporary root. The sync and async exports are
both exercised; the test does not duplicate the client implementation.

| Scenario through each facade | Real outcome checked |
| --- | --- |
| Startup refused | False result, one startup callback, no ping, no lock created |
| Daemon disappears during failed ping | Real private lock removed before failure; false result, one ping, no replacement startup |
| Existing daemon responds | True result, one ping, no startup, private lock remains until fixture cleanup |

There are six authored cases. Test-process PID metadata is used only when ping
will succeed or when the fixture removes that lock before returning a failed
ping. If removal fails, the callback returns success and records failure, so
even the old unsafe source cannot enter its PID-kill branch against the test
process. Actual unrelated processes are never used.

Native signal prevention is covered separately by the owned-sentinel suite,
also NOT_RUN. These callback cases do not qualify a full daemon, IPC protocol,
PID-reuse-safe lock lifecycle, explicit recovery or native runtime.
