# Existing POSIX platform lock test harness has stale ABI calls

Status: concrete source finding, unresolved; no test execution claimed.

`src/runtime/platform/test_unix_common.h` calls rt_file_lock with two arguments,
but the actual runtime.h and unix_common.h public ABI takes path pointer,
path byte length and timeout. Its comment names runtime_test.c as the includer;
that driver is absent at the reviewed release 5cecdd63a961de92ad5b54283ead0dd12af4e52d.

The new zero-timeout prevention test uses the exact public three-word ABI and
requires its own explicit legacy runtime.c provider profile. It does not repair
or claim execution coverage from this stale harness. Restore the driver and
all corresponding ABI calls in a separately owned harness repair before
admitting that existing suite as evidence.
