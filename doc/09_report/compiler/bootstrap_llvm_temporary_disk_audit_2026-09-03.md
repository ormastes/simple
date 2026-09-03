# Bootstrap LLVM temporary disk audit

Successful bootstrap LLVM emission copied `simple_llvm_<pid>.o` to the durable
output object but retained both the temporary object and textual `.ll` file.
For compiler-sized modules this leaves approximately `temporary object bytes +
textual IR bytes` per successful build, despite both being unnecessary after
the destination copy succeeds.

The fix deletes the temporary object after a successful copy and deletes the
textual IR unless `SIMPLE_KEEP_LLVM_IR=1`. Failure paths still preserve LLVM IR
for diagnosis. The durable copied object and architecture/link flow are
unchanged; the centralized temporary-root policy remains authoritative.

The focused regression verifies the cleanup set and explicit diagnostic-retain
policy. This is a lifecycle correction rather than an architectural rewrite.
