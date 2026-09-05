# Web Draw IR route cache retained serialized scenes

Status: implementation fixed; executable verification pending.

`src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl` embedded the full Draw IR SDN serialization in each of up to 16 route-cache keys. Large 4K scenes therefore remained duplicated after their frames were otherwise disposable.

The fix retains a bounded DJB2 fingerprint plus serialized byte length and keeps existing pixel fingerprint, command-completeness, device-identity, and pixel-count promotion checks. Hash collisions can at worst force validation/invalidation or a fallback route; they cannot bypass the existing current-frame pixel/device proof. Owner: web renderer memory lane. Unblock: run `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_draw_ir_route_key_memory_spec.spl` and measure retained-cache RSS on the 4K fixture through an admitted Stage-4 CLI.

