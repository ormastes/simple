# Windows XRay ring edges carry no timestamp, so profile time is 0

- Status: verification-pending
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

## Fix (2026-11-15, lane xrayts)
Ring ABI bumped to v2: `@__simple_xray_ring_v2` records are
`{ i64 site, i32 kind, i32 pad, i64 seq, i64 ts }` (32 B). The DLL edge stores
`ts = llvm.readcyclecounter()` before the release store of seq, and
`XrayWinFlagLeafV1.drain()` forwards it as the channel timestamp
(`xray_win_edge_record_stamped_v1`). Units are counter ticks, not ns.

- Repro row GREEN: `test/01_unit/lib/xray/xray_spy_backend_v1_spec.spl` 8/8
  (adds "drained timestamps are monotonic within a thread and time the profile").
- IR shape pinned: `test/01_unit/compiler/backend/xray_llvm_attrs_spec.spl` 27/27;
  leaf model `xray_win_flag_leaf_v1_spec.spl` 9/9.
- Per-edge cost (clang -O2 C model of the emitted edge, 2000 x 65536 edges, loaded
  host): v1 12.3-13.6 ns, v2 24.5-27.3 ns; 0 non-monotonic ts in one thread.
- Not run: a real `--xray` DLL built with the v2 ring (native run pending).
