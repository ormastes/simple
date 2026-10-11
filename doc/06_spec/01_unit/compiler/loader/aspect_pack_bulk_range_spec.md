# Aspect-pack bulk range copying

Executable source: `test/01_unit/compiler/loader/aspect_pack_bulk_range_spec.spl`.
This manual is derived from its actual four-case cached diagnostic, not from
placeholder results. Requirement ownership and unresolved admission gates:
`doc/08_tracking/bug/phase1_aspect_pack_windows_provider_owner_2026-10-11.md`.

| Scenario | Requirement | Actual asserted behavior |
| --- | --- | --- |
| Exported native byte-copy owner | REQ-APKIO-OWNER-002, REQ-APKIO-OWNER-004 | Read five known nontext bytes from a real mapped file, preserve each byte, then successfully unmap and delete the file. |
| Unaligned cross-granule range | REQ-APKIO-OWNER-002 | Copy 4096 bytes from offset 65531 in a 70000-byte fixture; compare every byte with its known original and delete the file afterward. |
| Invalid window geometry | REQ-APKIO-OWNER-003 | Reject negative delta, out-of-window extents, empty ranges and over-cap ranges before accessing the inaccessible synthetic pointer. |
| Pointer addition overflow | REQ-APKIO-OWNER-003 | Reject a max-i64 address plus a positive delta before invoking the native read owner. |

Evidence: `build/phase1-pack-io-20261011/bulk-spec-result.json` and
`bulk-spec.log`: 4 executed, 4 passed, 0 failed, exit 0.
Producer SHA256:
`15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
Executed product source SHA256:
`f6f505ee18a99d591923876ecd4f8d5874b7ec4c52028eb4012bf06ff7bffc54`.
Total diagnostic time: 66.39 seconds, including interpreted fixture generation
and per-byte assertions. This does not measure product-copy latency.

The binary-copy owner is the existing Simple `native_mmap_read_bytes`, backed
by the actual registered `rt_bytes_from_raw` provider. Matching raw descriptor
ownership was separately exercised before the spec. Positioned I/O stays with
its original open/seek/read/close provider when supported; unavailable open
falls back to the bounded raw mapping window.

Qualification: cached bootstrap diagnostic only. Qualified pure-Simple
compiler/core/MCP gates and platform performance verification remain pending.
These controls do not qualify an immutable archive or TOCTOU boundary.
