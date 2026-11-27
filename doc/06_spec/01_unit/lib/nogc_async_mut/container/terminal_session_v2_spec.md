# Tagged terminal-session dispatch V2

Status: **SOURCE-ONLY NOT_RUN; NO EXECUTABLE FIXTURE YET**. No tests or builds
were executed. No unit spec was created because this scope has no actual
retained-owner fixture. The scenarios below are not executable evidence and do
not establish acceptance coverage.

Source: `src/lib/nogc_async_mut/container/terminal_session_v2.spl`.

| Pending real-fixture scenario | Required observation |
|---|---|
| Legacy projection | An actual retained Legacy owner projects to its original V1 session |
| Windows projection refusal | An actual retained Windows owner rejects legacy projection without fabricating a process reference |
| Legacy read data | Actual process stdout text converts through checked boxed-byte extraction into a stdout chunk |
| Legacy read pending | Deferred stdout yields no chunks, no EOF, no error, and the original owner |
| Legacy read EOF | Only `process_stdout_eof` maps to EOF with an empty error |
| Legacy read failure | Reference/read/extraction failures retain the original owner and report the error |
| Windows read | Provider chunks, EOF, pending/no-data state and error propagate together with its returned canonical owner |
| Native validation | Each variant delegates to its actual owner's validation path |
| Identity | Mixed platforms compare false; Legacy delegates V1; Windows requires equal valid nonempty fingerprints |
| Legacy cleanup | Actual cleanup's returned owner, cleaned state and error propagate |
| Windows cleanup error | The returned owner remains retained and cleanup cannot report success |
| Windows absence required | An empty error without native absence evidence does not count as cleaned |
| Windows absence match | Cleanup succeeds only after the provider matches opaque absence evidence to its returned owner |

No pure session fixture is available in this worker's scope. V1 sessions contain
actual process ownership, and Windows connections and absence evidence are
opaque native owners. The existing constructors and native fixture harness must
provide those values before these scenarios can become meaningful assertions.
This manual claims neither passing tests nor a production-readiness gate. A real
Windows fixture must exercise pending reads, read errors and cleanup errors,
asserting that each result retains the actual returned canonical owner.

The union creates no Windows native owner. It preserves the returned owner even
on error, exposes no generic Windows process reference, and grants no input,
geometry, adoption, workload-completion or Host-settlement authority. Adoption
and application integration remain with the actual provider and target owner.
