# Atomic-write helpers use a fixed path.tmp name shared by concurrent writers

Severity: P1. Location: src/app/mcp/main_lazy_ctx_tools.spl:160-165; src/app/mcp/main_lazy_telemetry.spl:55-60; src/app/test_runner_new/test_runner_client.spl:41-49; src/lib/nogc_sync_mut/daemon_sdk/protocol.spl:47,136; src/lib/nogc_sync_mut/oauth2.spl:120; src/lib/nogc_sync_mut/privilege/store_fs.spl:34; src/lib/nogc_async_mut/process_set/ipc.spl:71; src/lib/nogc_async_mut/mcp/fileio_server.spl:398

## Interleaving
Two MCP servers (or two test clients) for one repo write the same store file concurrently.
1. A file_write(store.tmp, X); B file_write(store.tmp, Y) truncates and rewrites in place.
2. A rename(store.tmp, store) publishes whatever the file holds now (Y, or a torn mix if B is mid-write).
3. B rename(store.tmp, store) fails with ENOENT; callers ignore it (store write silently lost) or fall back to a plain write.

main_lazy_ctx_tools and main_lazy_telemetry use file_move_cross_device, which may copy then delete and is not atomic, exposing a partial file to readers. fileio_server.atomic_write_file shells out to mv and ignores its status.

## Fix
One helper atomic_write(path, content): tmp = path + ".<pid>.<counter>.tmp", write, fsync, rename on the same filesystem, delete tmp on failure; no plain-write fallback.

## Stress spec
Two processes write distinct 1 MB patterns to one path 1000 times each; a third reads continuously and asserts every read is exactly one of the two patterns.
