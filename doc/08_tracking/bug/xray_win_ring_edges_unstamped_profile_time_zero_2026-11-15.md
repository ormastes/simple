# Windows XRay ring edges carry no timestamp, so profile time is 0

- Status: open
- Found: 2026-11-15 (lane xrayshared)
- Repro: `test/01_unit/lib/xray/xray_spy_backend_v1_spec.spl`, the "every drained edge is stamped on both backends" row (`expected 0 to equal 4` for the Windows backend).

## Cause
`xray_win_edge_record_v1` (`src/lib/nogc_sync_mut/trace/xray_win_flag_leaf_v1.spl`)
passes `sequence = 0` and `timestamp = 0` to `trace_native_channel_record_words_v1`.
The emitted ring record `{ i64 site, i32 kind, i32 pad, i64 seq }` has no time
field, so `drain()` has nothing to forward. `trace_profile_fold_v1` therefore
gives `inclusive_ns = exclusive_ns = 0` on Windows. On Linux the handler shim
stamps each edge.

## Fix direction
The DLL edge has to capture time at the edge itself, for example a counter
stored in the ring `pad`/extra word, and drain must forward it. Stamping at
drain time would be wrong because it measures drain latency. This needs a
translator change to the emitted ring layout, which is owned by the xrayring lane.
