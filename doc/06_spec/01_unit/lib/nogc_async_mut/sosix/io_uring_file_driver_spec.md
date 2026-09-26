# Linux io_uring File Driver Scenario Manual

**Status:** Manual source map, not an execution receipt. Regenerate from
`test/01_unit/lib/nogc_async_mut/sosix/io_uring_file_driver_spec.spl` with the
current pure-Simple `spipe-docgen` before verification or release. Linux native
execution is required; a portable fallback does not satisfy these scenarios.

## Scenarios

1. **Exact provider selection.** Create the Linux driver, require the reported
   backend name to be `io_uring`, then close it.
2. **Positioned round trip.** Write 18 bytes at file offset three through the
   ring, read them at the same offset, and compare the returned buffer and
   transferred byte counts.
3. **Partial EOF and native error.** Read past EOF and require partial progress;
   read a missing path and require a negative native status.
4. **Cancellation retirement.** Cancel one submitted read, let the driver
   service it, pump the completion, and require exactly one successful lease
   release.
5. **Forged generation rejection.** Submit writes using a valid slot with a
   different file generation and a different buffer generation. Both must
   return `-22` without creating the host file; a forged buffer reference must
   expose no registered bytes.

The fifth scenario is a new provider-boundary regression check. The source is
the authority for exact assertions until the executable manual is regenerated.
