# Slang independent request-context detail design

Date: 2026-09-08. Status: implemented; focused native verification complete,
pure-Simple verification pending an admitted self-hosted runtime.

The native table has a fixed maximum and configurable admitted count. Slot
creation allocates every buffer and llama owner off-table, then publishes one
complete record. Handles encode no address. Closing increments slot generation;
model reload increments model generation, so stale handles cannot become valid
after reuse. Generation exhaustion fails closed.

Optional handle-taking ABI operations cover create/close, input reset/push,
tokenize, prefix prepare, prompt eval, sample, token eval, piece/output reads,
context size, and cooperative cancel. Existing symbols delegate to the selected
compatibility record. `backend.spl` admits S3 only when every symbol resolves
and the S3 capability bit is present.

Prefix acquisition pins a complete immutable entry before copying it into the
request context. Restore or truncation failure marks the entry unavailable for
new lookup, clears private request KV, and keeps bytes until existing pins
drain. Terminal cleanup releases a lease once even after decode/output failure.
Limit shrink stages an eviction plan and commits only if unpinned victims can
satisfy both count and bytes.

`close_backend` must propagate native busy/failure and retain the library handle.
Only a successful model teardown permits `spl_dlclose`. Request cancellation
sets a checked flag between native operations; no claim is made about preempting
an in-progress external kernel.

Implementation order: encapsulate all request globals; add generation handles;
add handle ABI and compatibility wrapper; add prefix pinning; expose Simple
request lifecycle; fix teardown; then add scheduler integration. Each slice
retains S2 as differential fallback.
