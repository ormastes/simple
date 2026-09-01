# Simple Web Server Native Live Smoke — 2026-08-11

Status: **RED**

The hosted web-server entry closure builds with the self-hosted stage-2 compiler when using Cranelift, and its configuration-only path runs. It does not establish a live listener: the native link generated unresolved stubs for `SyncTcpListener` and `SyncTcpStream`, the server process exited with status 1, and the loopback request was refused.

Authoritative receipt: `build/evidence/simple_web_server_live_smoke/receipt.md`.

Until a bounded live request observes an HTTP success status, `image/png`, PNG magic bytes, and a concurrent fast/slow scheduling result, this lane must not be presented as a runnable or performance-verified web server.
