# WebSocket mask verification plan

Scope: `websocket_timestamp_owner_and_entropy_2026_10_16`, masking follow-up to
handshake candidate f2c3f80419f. Interface review: Astra_enum approved Result
migration, unmasked bypass, complete fragment failure, CDP failure sequencing,
drain_events errors, and Electron cleanup before propagation.

No admitted Simple runtime is available. All execution below is UNRUN; this
plan does not count as executable failure injection or measured coverage.

1. Run the twelve nonce-independent mask SSpec examples on an admitted producer.
   Record source/producer/runtime/provider hashes and registered/executed counts.
2. Link the actual entropy provider with a controlled fill failure at the
   provider boundary. Exercise every masked frame/close/fragment entry point;
   assert Err and no frame/partial collection escapes. Fail on the second
   fragment too, proving earlier frames are not returned. Restore provider
   success and verify a new independent four-byte request per frame.
3. With loopback CDP peer and the same actual-provider fault injection, exercise
   send, send_on_session, pong on received ping, and close. Count peer bytes:
   zero application frame bytes after failed key acquisition. Send failures
   must precede pending-command insertion. Pong/close failures must close once,
   set closed, stop buffered-frame processing, and not become a timeout/success.
4. Exercise drain_events and wait_for_event after pong entropy failure. Assert
   transport Err. Exercise Electron close with CDP failure; verify process
   cleanup still happens and then transport Err is returned.
5. Force entropy failure while sending unmasked server binary/close frames:
   no entropy call is made and exact normal wire bytes are preserved.
6. Compile all transparent reexport families and actual CDP/async callers.
   Verify consumers of the changed Result signatures, then required core/lib,
   MCP/LSP checks and env/process guards under the admitted runtime policy.

The tracked pre-change source/example/script/test caller inventory found 24
call expressions across the migrated owners; facades are transparent exports.
No concrete CDP drain_events consumer was found. Existing unrelated database
and Simple Lab methods with that name are not CDP callers.

Owner: proto_http_redirect. Reviewer: Astra_enum. Landing: land_source_repairs.
No seed/bootstrap/vendor builds are authorized by this plan.
