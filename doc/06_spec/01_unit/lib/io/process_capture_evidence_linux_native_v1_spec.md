# Linux native capture evidence prerequisite specimens

Status: **NOT_RUN**, four source-authored scenarios. Corresponding source:
`test/01_unit/lib/io/process_capture_evidence_linux_native_v1_spec.spl`.

Required setup: native Linux observation provider, actual main thread, genuine
retained procfs origin, GNU-compatible `/usr/bin/printf` octal-byte formatting
and `/usr/bin/sleep`. Missing setup fails; no skip or synthetic native receipt.
Linux worker-thread use is unsupported by this new facade even if another
existing observation API can execute in that context.

1. Real finite printf preserves actual combined EOF, native seen/kept/reap/error
   facts, exact CLI exit and delivered bytes. Returned byte copies do not
   mutate the opaque receipt. No per-stream EOF is manufactured.
2. Real printf emits byte255; copied owner A collects and positively retires,
   while invalid UTF8 keeps raw bytes and the first decode diagnostic. Alias B
   retries and cancels against the same closed tombstone with no new evidence
   or resurrected owner and sees the same diagnostic. This is real completion
   and alias behavior, not an injected native cleanup-fault claim.
3. Real longer printf under a four-byte stdout cap preserves actual truncation
   and retained bytes, without replacing the native EOF fact with exit/limit
   inference.
4. Real sleep is canceled through its exact existing observation owner, then
   actual native cancellation/reaping/retirement facts are checked.

The finite helper retains every returned owner immediately, attempts exact
cleanup in after_each and refuses a new admission if prior cleanup remains.
The underlying collect remains synchronous with its existing bounded25ms
poll loop. All four scenarios are NOT_RUN. Partial native allocation,
projection/close/kill faults, fork/PID-namespace fault qualification, delayed
descendants and live engine/managed environment integration are NOT_COVERED.
