# Packed frontend encoder repeatedly copies growing byte buffers

The old native producer (SHA256
`6304c166acbcac0a1ea78534fc9a5859507a87ad655eabf98618c798045ad6e8`)
showed excessive allocations while parsing a synthetic 16-field module.
LLDB boundary observations localize the jump to `frontend_spab_store_v1`:
RSS rose from 20,188 to 239,308 KiB. The parser, flat-pool line dump and
AST conversion remained around 17–20 MiB. With the supported
`SIMPLE_FRONTEND_SPAB=0` text-cache route and a fresh cache, store RSS moved
from 21,624 to 21,976 KiB; first parser scope-end RSS was 23,008 rather than
241,156 KiB. These are controlled diagnostics stopped deliberately at the
scope boundary, not successful compiler builds or manager qualification.

The private packed byte helpers copied `out` into `buf` on every scalar,
append and padding operation. Frozen native `_put_le` disassembly resolves
its first indirect call (GOT 0x24ce580) to `rt_array_copy` at 0x1f7b47c.
Repeated scalar writes therefore copy progressively larger buffers and retain
quadratic cumulative scratch allocations until the owner reclaims them.

The fix marks these private destinations `mut out` and appends directly.
All callers supply fresh local construction buffers or exclusively owned
`_Emit` child buffers. Tails remain readonly, no destination aliases its tail,
and child buffers are published into sections only after construction. Public
encoder inputs and the packed format, hashes, validation and authority rules
are unchanged. No cache or safety check is disabled by the source fix.

## Validation

- Actual production packed-format SSpec: one file, nine tests executed, nine
  passed, zero failed, wrapper exit 0. Covers every pool shape, deterministic
  bytes, aligned layout, digest/tamper rejection and repeated growing encodes
  preserving caller inputs. This was the explicit Rust-seed diagnostic route,
  not native SSpec qualification. Log `/private/tmp/astra-packed-encoder-mut-final-seed.log`,
  SHA256 `0f810c4ab930a451d0a90b51fbd7937935e7ba45aaf5ba16bd430bc0c75693df`.
- Native mutable-buffer ABI control: build/run exit 0, exact stdout
  `OWNED_APPEND_OK` plus LF. Both old copying and new mutable helper produce
  identical 2,048 golden little-endian bytes after 256 scalar appends.
  LLDB counted 256 `rt_array_new` calls from the copying helper, zero from the
  mutable helper, and two initial arrays from main. This tests the lowering
  contract used by the fix; it is not the full production encoder closure.
  Artifact SHA256 `d81aa4e2688dd9c5a54a23cef032d2609311a6d8d300ba5b9f670f810cba762c`;
  build peak 515,300 KiB under the 524,288 KiB bound, quiescent receipt.
  Fixture: `test/fixtures/compiler/packed_encoder_owned_buffer_probe.spl`.
- The first control attempted a Rust-only auxiliary counter unavailable in
  the core-C artifact and failed linking; it executed no control. The corrected
  control uses actual LLDB allocation-call counts. No missing symbol is ignored.

Host evidence root:
`/private/tmp/buildrunner-linux-lane-20261029/hir-retention-repro/results`.
`boundary16/store.log` SHA256
`2a6603dd539d66dc764fb073524e171ba87b9cb80928a2f4dd457e66d8495b9e`;
`boundary16/text.log` SHA256
`e63af426c8d332136bbb3ec5fa03c529cd5ee2c728d8ba9c2e250c1376ea02e9`;
`append-owned/lldb.log` SHA256
`f7638f4ddfe21a22cfdaa3a74bd0c34a1db080e3dd50a23c79b701143995dac8`;
`append-owned/build.log` SHA256
`44199e2b0986589b13cc4213109403e1cf8785dcdef6e6ab5c56a75d38304c03`.

A rebuilt producer must validate the complete packed encoder's native memory
improvement. Full manager and BuildRunner Hello admission remain separate work.
