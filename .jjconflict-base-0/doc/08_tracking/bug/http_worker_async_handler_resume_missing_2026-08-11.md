# HTTP worker cannot safely resume asynchronous SSR handlers

## Impact

REQ-003/REQ-004 cannot be satisfied by attaching the canonical renderer directly to the current production HTTP worker. Matched routes currently use `inline_static_handler`; handler dispatch returns synchronous `HttpResponseData`, and the worker/connection state has no pending-response completion, cancellation, or timeout state. Calling the GC-profile semantic/layout -> `DrawIrComposition` -> Engine2D renderer inline would block unrelated connections.

## Required fix

Add a typed async handler lifecycle owned by the existing worker/connection path: bounded submit, pending connection identity, completion polling/delivery, disconnect cancellation, timeout, overload response, and drain cleanup. Then connect the bounded renderer mailbox through that interface. Do not add a second accept loop, a private font/render path, an unreachable queue, or per-request source-file reads.

## Verification

- Concurrent slow SSR and fast static requests prove the fast response is not head-of-line blocked.
- Disconnect, timeout, queue-full, and shutdown scenarios reclaim the pending job exactly once.
- Live SSR evidence traverses web semantic/layout, emits `DrawIrComposition`, lowers through Engine2D, and captures independent semantic and pixel/readback evidence.

