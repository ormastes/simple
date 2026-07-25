# Host-GPU Image-Resource Retention

No dedicated guide for the SimpleOS host-GPU protocol/capability system
existed prior to this doc (checked `doc/07_guide` for `host_gpu`/`ivshmem`
coverage: `qemu_system_tests.md` documents running the QEMU check scripts
for the ivshmem transport generally, not the protocol's capability
negotiation or wire layout — so this is a new guide, not an extension).

Image-resource retention is a capability-negotiated wire optimization for
the SimpleOS host-GPU ivshmem transport: instead of re-sending full pixel
bytes for an image resource every frame, the guest can send a 72-byte
id+checksum reference once the host has already accepted the full image
and the checksum still matches. Landed `42de88d527c` (spec 6/6, probe
13/13).

Governing plan:
`doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md`
(landed `d1d22404912` on `origin/main`). This feature is **slice item 8**
("persistent per-window GPU surfaces"), and the plan's coordinator verdict
scopes it explicitly: "Item 8 (persistent GPU surfaces) is host-side-first:
resource-revision retention in the ivshmem path can be built and
unit-proven without QEMU; the in-guest proof rides the existing OVMF
evidence gate, serialized with the other QEMU lanes." The "not proven
end-to-end in QEMU" note under "Open ceilings" below is therefore this
landing executing exactly that constraint, not an unaddressed gap. Item 8
depends on item 7 (DrawIR patch — see
`doc/07_guide/ui/rendering/draw_ir_incremental_patch.md`) as its enabler,
per the plan.

Touches:

- `src/lib/common/gpu/simpleos_host_gpu_protocol.spl` — wire offsets,
  capability constants, reason codes
- `src/lib/common/gpu/simpleos_host_gpu_draw_ir.spl` — retained entry
  encode/decode + host-side table resolution
- `src/os/lib/gpu_bridge/host_gpu_ivshmem.spl` — guest-side negotiate/submit
- `src/app/simpleos_gpu_host/main.spl` — host daemon request loop
- `src/os/compositor/engine2d_wm_frame_executor.spl` — the one production
  call site that actually uses the retained submit path

## Capability handshake

Two new wire offsets in `simpleos_host_gpu_protocol.spl`, additive to the
existing HELLO layout (never changes offsets/semantics above them):

| offset | field | direction |
|---|---|---|
| 280 | `SIMPLEOS_HOST_GPU_WIRE_REQUESTED_CAPABILITY_MASK` | guest -> host |
| 288 | `SIMPLEOS_HOST_GPU_WIRE_NEGOTIATED_CAPABILITY_MASK` | host -> guest |

`SIMPLEOS_HOST_GPU_CAPABILITY_IMAGE_RESOURCE_RETENTION = 1`;
`SIMPLEOS_HOST_GPU_CAPABILITY_SUPPORTED_MASK` currently equals it (the only
capability defined so far). Both slots are staleness-defended, because the
backing ivshmem region can be reused across sessions: the guest
(`host_gpu_ivshmem_negotiate`) writes `REQUESTED_CAPABILITY_MASK` and
pre-clears `NEGOTIATED_CAPABILITY_MASK` to 0 on every HELLO publish, and the
host (`_process_request` in `main.spl`) **reads then immediately clears**
`REQUESTED_CAPABILITY_MASK` back to 0 — a read-then-clear, single-use slot.
This stops an old guest binary that never writes the field from handing the
host a byte left over from a *different, newer* guest that shared the same
backing file in an earlier session. A capability is only ever honored when
**both** sides freshly asserted it in the same HELLO round; the negotiated
mask is re-read straight off the wire at every point of use (`main.spl`'s
DRAW_IR handler, `host_gpu_ivshmem_submit_draw_ir_retained`) — **never
cached** in a struct field that could go stale across frames.

## Full vs reference wire records

`SimpleOsHostGpuImageResourceEntry` (`simpleos_host_gpu_draw_ir.spl`) is
either a **full** record (`is_reference: false`, carries `pixels`) or a
**reference** record (`is_reference: true`, carries only `pixel_checksum`,
zero pixels). Both share a 56-byte header
(`SIMPLEOS_HOST_GPU_IMAGE_RESOURCE_ENTRY_HEADER_BYTES`: record_bytes, kind,
uri_count, width, height, pixel_count, pixel_checksum — all u64le) plus an
8-byte-aligned URI and (for full records) 8-byte-aligned pixel bytes. This
is a distinct wire record type from the pre-existing plain
`SimpleOsHostGpuImageResource` codec (`simpleos_host_gpu_image_resources_
encode`/`decode`) — that codec's byte output is never touched by the
retention extension, so a plain/legacy session sees byte-identical wire
behavior to before this feature landed.

For a 64x64 ARGB icon (16384 pixel bytes, verified against
`test/01_unit/lib/common/gpu/simpleos_host_gpu_image_retention_spec.spl`):
a full entry is 56 (header) + 16 (URI `"asset://icon-64"`, 15 bytes padded
to the 8-byte alignment) + 16384 (pixels, already 8-aligned) = **16456
bytes**; a reference entry for the same image is 56 + 16 + 0 = **72 bytes**
— a 99.6% reduction (`(16456-72)/16456`).

The content-revision key for a full entry is
`simpleos_host_gpu_readback_checksum` — the **same, pre-existing** additive
readback checksum, not a new hash. It is order-insensitive and
collision-weak (see "Open ceilings" below).

## Guest side: deciding full vs reference

`host_gpu_ivshmem_submit_draw_ir_retained()` (`host_gpu_ivshmem.spl`) is
the retention-aware submit. If the session did not negotiate the
capability (checked by re-reading `NEGOTIATED_CAPABILITY_MASK` off the
wire), it delegates straight to the pre-existing
`host_gpu_ivshmem_submit_draw_ir()` — byte-identical wire output to before
retention existed. When negotiated, for each image resource it computes
the current pixel checksum and compares against `sent_resources` (a
`[SimpleOsHostGpuImageResourceRevision]` the caller threads in from the
prior frame): checksum match -> encode as a reference; otherwise -> encode
full. It returns `HostGpuIvshmemDrawIrResult { receipt, sent_resources }`,
and **`sent_resources` is empty on any non-PASS receipt** — fail closed, so
the caller's next frame re-sends everything full rather than assuming the
host still has what it last accepted.

The one production caller is `Engine2dWmFrameExecutor`
(`engine2d_wm_frame_executor.spl`), which holds
`image_resource_revisions: [SimpleOsHostGpuImageResourceRevision]` as
per-executor state, calls `host_gpu_ivshmem_submit_draw_ir_retained()` each
frame, and stores `result.sent_resources` back into that field for the next
frame.

## Host side: revision table, fail-closed resolution

The host daemon (`main.spl`) threads a `retained:
[SimpleOsHostGpuImageResource]` table through its per-connection loop state
(`SimpleOsGpuHostLoopState`). **The table is cleared to `[]` on every HELLO
the daemon processes — success or failure** — so retained ids can never leak
across a guest reboot on a reused backing file. On a DRAW_IR request, if
retention was negotiated (re-read from the wire, never cached), the host
decodes entries with `simpleos_host_gpu_image_resources_decode_retained()`
and resolves them via `simpleos_host_gpu_resolve_retained_images(entries,
retained)`:

- A **reference** whose `image_uri` is missing from the table, or whose
  checksum no longer matches the table's cached checksum (recomputed via
  `simpleos_host_gpu_readback_checksum`, not trusted from the wire) ->
  resolution fails closed: `ok: false`, the input table is returned
  **unchanged**, and the daemon responds with the new reason code
  `SIMPLEOS_HOST_GPU_REASON_UNKNOWN_IMAGE_RESOURCE` (value 15). The guest
  sees a non-PASS receipt and, per the fail-closed contract above, resubmits
  everything full next frame.
- A **full** entry resolves as given and is upserted into the table
  returned for the next frame's lookups.

A plain/legacy session (retention not negotiated) is routed to the
untouched `simpleos_host_gpu_image_resources_decode()` +
`simpleos_host_gpu_image_resource_coverage_reason()` path — unaffected by
any of the above. This is also the fallback for a version mismatch: the
protocol version constant itself did not change (`SIMPLEOS_HOST_GPU_
PROTOCOL_VERSION` stays 1) for this feature, so an old host paired with a
new guest (or vice versa) simply never negotiates the capability and both
sides run the pre-existing full-resource path.

## Open ceilings (recorded, not silently accepted)

- **Collision-weak revision key.** The revision/content key reuses
  `simpleos_host_gpu_readback_checksum`, an order-insensitive additive
  checksum. A genuinely changed image whose pixels happen to sum to the
  same value would be (mis)treated as unchanged both by the guest (deciding
  full-vs-reference) and by the host's staleness check (comparing the same
  checksum) — neither side would catch the collision. A position-sensitive
  hash is required before this checksum is trusted as a production
  content-revision key; sanctioned for this slice only because it reuses an
  existing shared code path with low real-content collision rate.
- **No table eviction.** The host's `retained` table only clears on HELLO;
  within a session it grows with every distinct `image_uri` a full entry
  introduces and is never bounded or evicted. Long-running sessions with
  many never-repeating image ids will grow this table unboundedly.
- **Scope stops at image resources.** Scene/DrawScene-level retention
  (`CREATE_DRAW_SCENE`/`APPLY_DRAW_PATCH` from the host-GPU persistent
  protocol model referenced in `main.spl`'s own comments) is a later phase,
  not implemented here.
- **Not proven end-to-end in QEMU yet — by plan, not oversight.** The
  governing plan's coordinator verdict scopes item 8 as "host-side-first":
  unit-provable without QEMU, with the in-guest proof deliberately deferred
  to ride the existing OVMF evidence gate, serialized with the other QEMU
  lanes. This landing has unit-spec coverage
  (`test/01_unit/lib/common/gpu/simpleos_host_gpu_image_retention_spec.spl`,
  6/6) exercising the encode/decode/resolve logic directly; there is no
  QEMU-gated evidence (per the repo's board-runnable/real-firmware rule)
  yet that the guest-MMIO negotiate/submit path and the host daemon loop
  actually exchange a live reference over ivshmem end-to-end. It rides the
  same OVMF gate as the rest of the host-GPU ivshmem transport
  (`scripts/check/check-simpleos-qemu-host-gpu-2d.shs`), but that script was
  not re-run against this feature as part of this doc.
