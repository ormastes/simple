# SCV native draft sync v1 test plan

Executable specification: `test/03_system/app/scv/feature/scv_gateway_draft_sync_v1_spec.spl`.

- Prove a PUT and GET cross a real loopback TCP socket through the native
  bounded client and production HTTP request handler.
- Assert binary NUL and non-UTF8 bytes survive, the PUT returns the exact
  principal/digest/count `local_durable` receipt, exact retry is idempotent,
  and GET is marked `local_readback`.
- Unit coverage rejects non-loopback or unprovisioned roots, malformed and
  principal-bearing requests, wrong credentials, repository mismatch,
  read/write capability violations, noncanonical base64, payload over-limit,
  forged principal, and forged receipt count. CLI coverage checks all three
  draft routes and fail-closed listener startup.
- Verify the existing 4 KiB transport caller remains capped while the opt-in
  draft transport has an independent hard ceiling.

The tests-first spec commit is `874fd69b899`. Runtime results remain
`NOT_RUN`: this checkout does not contain the pure-Simple `bin/release`
runtime. Do not substitute the Rust bootstrap seed. Run unit specs and this
system spec with the admitted self-hosted runtime before treating behavior as
runtime-qualified.
