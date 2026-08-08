# Runtime compiler temporary namespace hardening

## Open risks

Runtime C objects use `simple_rt_<pid>_<raw-target>_<stem>.<ext>` paths. Two
hosted links for the same target running concurrently inside one process can
write and delete the same objects. Separate processes are PID-isolated, but PID
reuse can encounter stale files. The raw target text is also embedded directly
in the filename; current hosted-target admission narrows accepted values but a
future target surface must not permit path separators to escape the temp owner.

## Required prevention

Give every hosted link invocation its own deterministic staging directory or
nonce, and sanitize or hash the target component before creating paths. Add a
same-process parallel-link collision regression plus hostile target-component
tests. Do not treat tracking only the successfully created prefix as a fix: it
would leave the concurrent write collision intact.

This is intentionally separate from the landed early-error cleanup fix, which
correctly deletes the current full planned list but does not create the shared
namespace risk.
