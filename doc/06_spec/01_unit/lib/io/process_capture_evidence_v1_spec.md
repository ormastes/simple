# Owned capture evidence V1 source manual

Status: **NOT_RUN**, all eleven source-authored cases. No generated PASS claim.

`test/01_unit/lib/io/process_capture_evidence_v1_spec.spl` has six production
helper cases: additive legacy result defaults keep unknown facts absent;
native collect retirement excludes EAGAIN/EBUSY and does not imply EOF/success;
byte copies preserve NUL/invalid UTF8 independently of caller mutation; exact
per-stream bounds are admitted; invalid deadline/grace/path/NUL args refuse.
The sixth case tests the actual sticky-first-diagnostic/positive-retirement
progress reducer: a raw stale diagnostic remains unretired, positive consumed
retires monotonically, and the first diagnostic survives. These cases do not
manufacture opaque native evidence.

`process_capture_evidence_linux_native_v1_spec.spl` has four actual native
prerequisite specimens. Existing observation capabilities, actual Linux main thread with genuine
procfs origin, and actual
`/usr/bin/printf` and `/usr/bin/sleep` are required. Missing setup fails. The
cases inspect actual complete EOF/counts/result and independent byte getter
copies, actual four-byte truncation, actual same-owner cancellation and retirement, and a genuine
invalid-UTF8 completion followed by copied-owner retry/cancel against the
canonical retired tombstone. The truncated case does not replace the real EOF fact with an
exit/limit inference. All are NOT_RUN.

`process_capture_evidence_windows_native_v1_spec.spl` has one actual native
canonical-thread specimen using installed
`C:/Windows/System32/whoami.exe`, clean explicit SystemRoot environment, exact
cwd and a genuine sampled expiry. A finite512-turn loop yields10ms only in
fixture code. It checks real per-stream/combined EOF, terminal and cleanup,
while unseen counters, POSIX reap and unsupported identity/error facts remain
nil. Raw bytes survive a localized non-UTF8 code page. Missing actual Windows
setup fails; it is not a Linux/native-success substitute. NOT_RUN.

Native fixture cleanup retains the actual turn owner immediately. Before a
new admission it must finish any prior retained owner, or fail without
overwriting it. after_each attempts bounded exact cleanup and explicitly fails
if ownership remains; abrupt external runner termination is not cleanup proof.

NOT_COVERED: partial native allocation/projection errors, close/termination
failures, descendants holding output pipes, malformed native receipt delivery,
cross-thread runner behavior, ABI/link or scheduler qualification, managed
environment/container-provider integration, live engines and latency/RSS.
Pure cases are not evidence that those native paths executed.

Matching native manuals: `process_capture_evidence_linux_native_v1_spec.md`
and `process_capture_evidence_windows_native_v1_spec.md` in this directory.
