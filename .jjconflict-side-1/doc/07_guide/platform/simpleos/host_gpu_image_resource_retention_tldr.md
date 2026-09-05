# Host-GPU Image-Resource Retention — TL;DR

Capability-negotiated wire optimization: guest sends a 72B id+checksum
reference instead of full pixel bytes when the host already has the image
and the checksum matches. New guide (no prior dedicated host_gpu/ivshmem
protocol doc existed). Slice item 8 of `web_wm_gpu_3d_review_2026-07-20.md`
(host-side-first by plan). Landed `42de88d527c`, spec 6/6, probe 13/13.

```
HELLO: guest writes REQUESTED_CAPABILITY_MASK(280) -> host writes
       NEGOTIATED_CAPABILITY_MASK(288); both single-use/re-cleared per
       round (never cached); table CLEARED on every HELLO (success or fail)

DRAW_IR frame (retention negotiated):
  guest: checksum(pixels) == last-accepted? -> REF(72B) : FULL(16456B for 64x64)
  host:  ref unknown-uri or checksum mismatch -> FAIL CLOSED
         (REASON_UNKNOWN_IMAGE_RESOURCE=15, table UNCHANGED, guest resends full)
  full:  resolved + upserted into host's `retained` table
  only production caller: Engine2dWmFrameExecutor.image_resource_revisions
```

Old/new protocol mixes: PROTOCOL_VERSION stays 1 either side just never
negotiates the capability -> falls back untouched to the pre-existing full
codec (byte-identical wire output).

Open ceilings: revision key = reused order-insensitive readback checksum
(collision-weak); no table eviction; scene/DrawScene retention is later;
guest-MMIO/daemon path has unit-spec coverage only — QEMU/OVMF proof deferred by plan.

Full guide: [host_gpu_image_resource_retention.md](host_gpu_image_resource_retention.md)
