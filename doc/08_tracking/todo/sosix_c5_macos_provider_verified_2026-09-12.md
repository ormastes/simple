# SOSIX C5 macOS provider evidence

Status: open; native macOS asynchronous file provider not implemented.

`src/lib/nogc_async_mut/sosix/file_driver.spl` previously referenced this
missing record. Its comment records a 2026-09-12 portable-driver run; this
document preserves that attribution without claiming a new passing run.

The 2026-09-21 aarch64-apple-darwin audit at source `20245f731db` found a
portable `file_read_text_at`/`file_write_text_at` driver, with no kqueue or
`dispatch_io` file-operation provider to bind. The portable driver cannot
establish native asynchronous-provider parity. TODO 306 remains open.

The attempted current `file_driver_spec.spl` run used admitted bootstrap
Phase 2 SHA256
`9aea8349b6fb411e46b325ecff70d2924173533d4c2e71d41e2619e9998c41a1`;
it exited 1 with `error: unknown command 'test'` before executing any case.
The runner requires a test-capable admitted self-hosted binary. No Rust seed
fallback was used.

Completion requires an owned Darwin provider with real asynchronous submit,
completion, cancellation, and lifetime evidence, then positioned read/write,
short-read, missing-file, and invalid-window assertions on this Mac. Keep the
portable provider available while that implementation is absent.
