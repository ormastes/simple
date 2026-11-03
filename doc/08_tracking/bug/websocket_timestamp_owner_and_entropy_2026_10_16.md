# WebSocket undefined clock owner and predictable nonce/mask generation

Date: 2026-10-16. Status: source workaround prepared; native verification UNRUN.

Both nogc_sync_mut/websocket/handshake.spl and frame.spl referenced undefined Platform.timestamp(). Current source and inspected historical aff29/d3fb-parent source provide no corresponding owner. The compile workaround imports the genuine std.nogc_sync_mut.io.time_ops.current_time_ms implementation. Historical timestamp units are unknown; behavioral equivalence of the clock replacement is NOT established.

The existing handshake nonce and frame-mask formulas reduce time modulo 256. Each therefore has at most 256 seed states. Replacing the clock does not repair entropy or qualify these algorithms as secure. The genuine crypto.entropy_platform.entropy_platform_bytes(count:u64)->Result<[u8],text> owner supplies exact-fill entropy and wipes failures. A security repair must request 16 nonce bytes / 4 mask bytes and propagate entropy failure through actual callers without empty or time-derived fallback. That API/caller change is outside this compile workaround and remains open.

Related historical removal: async JS URL helpers were intentionally removed in 133e416e098. Only their five stale explicit facade exports (_scheme, _origin, _without_fragment, _without_query, _base_dir) were removed; private browser-page helpers and all other exports remain unchanged.

## 2026-11-03 — fix implemented, verification pending

Clock owner removed and nonce/mask sourced from `entropy_platform_bytes` by
`f084439916d` and `29cbca94892`. Their specs were AUTHORED_UNRUN; run under
`bin/simple.exe test` they failed 7/12 (`websocket_mask_entropy_spec`) on
`val x = []` + `push` (immutable array) and `char_at(i).byte_at(0)` in
`ws_handshake_text_to_bytes`. Both fixed in `work/b2-websocket-mutable-arrays`
(mask spec 11/12, nonce spec 3/4, collision spec 2/2). The one remaining red
case per spec is `unknown extern function: rt_entropy_fill`: the extern is
declared in `entropy_platform.spl` / `rsa_pkcs1.spl` but has no runtime
definition anywhere under `src/` — a runtime backing gap, not a websocket bug.
Close once `rt_entropy_fill` is backed and both specs are green.
