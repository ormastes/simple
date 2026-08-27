# SOSIX FS v1 Registered-Buffer Client

The caller creates a reply endpoint, discovers the filesystem service endpoint,
and supplies both as authenticated-kernel inputs. The client never invents an
endpoint or a capability right.

The owner-managed table copies bytes into at most 64 planner-side registrations. A reference
contains only a slot and nonzero generation; unregistering drops the owned bytes
and advances the generation before that slot can be reused. Stale references,
owner substitution, invalid access masks, and out-of-range transfers fail closed.
Because the table is a public value, every lifecycle and submission entrypoint
also validates its canonical shape before use: the owner must be nonzero, the
entry count bounded, each slot/index and generation valid, each entry owned by
the table owner, active entries nonempty with known access, and retired entries
cleared. A malformed table is returned unchanged as `buffer-table-corrupt` and
is never reused or dispatched.

Local registration grants no service authority. Planning additionally requires
an authenticated service receipt binding the owner, service endpoint, buffer
slot/generation, nonzero service registration ID, and owned-copy memory mode.
Reads require service-write access and writes require service-read access.

An accepted submission reuses the filesystem v1 client adapter and codec to
produce the 88-byte pointer-free request. Execution invokes owned-copy syscall
132 exactly once. The payload address exists only at the local syscall copy-in
boundary, is never encoded on the wire, and no receive or blocking wait occurs.
Kernel rejection is returned as rejection; it is never converted to success.
Because the execution plan is a public value, execution revalidates its
canonical planner facts before crossing the syscall boundary: `ready`, zero
status, nonzero service and reply endpoints, a supported positioned API, and a
nonempty payload. Forged accepted plans fail closed without dispatch.
