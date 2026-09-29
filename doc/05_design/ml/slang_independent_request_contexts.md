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

API migration: backend cleanup operations are named `close_backend_request`
and `cancel_backend_request` (formerly `close_request` and `cancel_request`).
The lifecycle semantics are unchanged: both terminate the native
`GgmlRequest`. Compatibility aliases are intentionally absent because those
global names collide with `KvPageManager` members and caused incorrect WFFI
dispatch. Physical-page configuration and activation use a fixed-format scalar
text configuration at cross-module boundaries until typed integer argument
tagging is fixed; the owning module accepts only nonnegative decimal signed-64
values, and malformed, signed, or overflowing scalar text is rejected.

The exact API migration is:

- `engine_set_n_ctx` -> `engine_set_n_ctx_text`
- `engine_set_matched_cpu_threads` -> `engine_set_matched_cpu_threads_text`
- `engine_set_physical_pages` -> `engine_set_physical_pages_config`
- `paged_executor_activate` -> `paged_executor_bind_backend` followed by
  `paged_executor_activate_config`
- `physical_page_pool_create` -> `physical_page_pool_create_request`

Binding transfers one pending backend reference to the paged executor. The
caller must immediately activate it or call
`paged_executor_clear_pending_backend`; `paged_executor_shutdown` also clears
an abandoned pending binding as the lifecycle recovery path.

`close_backend` must propagate native busy/failure and retain the library handle.
Only a successful model teardown permits `spl_dlclose`. Request cancellation
sets a checked flag between native operations; no claim is made about preempting
an in-progress external kernel.

Implementation order: encapsulate all request globals; add generation handles;
add handle ABI and compatibility wrapper; add prefix pinning; expose Simple
request lifecycle; fix teardown; then add scheduler integration. Each slice
retains S2 as differential fallback.
