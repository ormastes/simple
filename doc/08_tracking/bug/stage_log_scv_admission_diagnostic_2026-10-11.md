# Stage log guard omitted an emitted SCV admission reason

Status: source fix; shell regression verified separately from compiler qualification.

Attempt07 at source26a5cb014d4bc61c8657f08799160f9f17834379 stopped before
module compilation with exit1. Its194-byte native log under
`C:/dev/simple-bootstrap-storage/rp3g-20261011/logs/x86_64-pc-windows-msvc/stage2-native-build.log`
contained `SCV-E-ADMISSION: compile-event-journal-missing` and the supported
cold-init instruction. The stage-log guard reported it as undiagnosable because
its broad legacy pattern omitted this anchored diagnostic code.

The guard now uses the existing `bootstrap_scv_admission_diagnostic` owner for
SCV-bearing lines with nonempty reason text on both primary and sibling-log paths.
The shared owner's bare-code acceptance is insufficient for this guard.
Such lines are excluded
from the broad legacy matcher: a quoted/parser line containing `error:` must
not become evidence of an emitted SCV error. Other diagnostic patterns remain.

`scripts/bootstrap/tests/stage-log-scv-diagnostic-test.shs` consumes the shared
positive/negative owner fixtures, reproduces the attempt07 text with CRLF,
checks sibling attribution, mixed real/quoted errors and absent evidence.
The guard's existing selftest covers its other diagnostic/resource cases.
Diagnosable means the failed stage has a reason; it does not make the stage pass.
No compiler retry, source-inventory relaxation or receipt mutation is included.
