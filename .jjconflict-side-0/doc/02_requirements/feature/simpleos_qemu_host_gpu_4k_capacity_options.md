<!-- codex-research -->
# SimpleOS QEMU Host-GPU 4K Capacity — Feature Options

User selection is required before changing the existing 8 MiB requirement.

## Option F1 — Protocol v2 with a fixed 32 MiB arena (recommended short path)

**Description:** Introduce protocol v2 with one coordinated 32 MiB shared
region. Relocate/generalize the AArch64 and RISC-V BAR assignments, use a
32 MiB-safe x86 window, and reject v1/v2 mixed peers explicitly. Preserve the
current one-request/one-readback protocol.

**Pros:** Smallest route to exact current 3840x2160 production frames; preserves
whole-frame checksum, one-request/one-receipt flow, O(1) auxiliary presentation
memory, and the current lifecycle; lowest latency and implementation surface.

**Cons:** Requires coordinated guest/daemon/wrapper deployment; does not fit
4096x4096 or arbitrary totals of multiple large IMAGE resources; consumes
24 MiB more shared address space per active guest.

**Effort:** M, approximately 11–12 files.

## Option F2 — Versioned negotiation of 8/32/128 MiB arenas

**Description:** Keep v1 at 8 MiB and add a versioned capacity contract that
discovers the BAR/backend size and negotiates one supported bound. Generalize
daemon mapping, guest validation, and per-ISA BAR ownership.

**Pros:** Retains explicit v1 compatibility; supports small probes, current 4K,
and the existing 4096x4096 dimension ceiling at the 128 MiB tier; avoids paying
maximum capacity for every run; best long-term protocol shape.

**Cons:** More runtime validation and compatibility branches; BAR-size discovery
and all three architecture adapters change; larger test matrix and invalidation
surface.

**Effort:** L, approximately 12–18 files.

## Option F3 — Protocol v2 tiled transfer within 8 MiB

**Description:** Upload and return bounded tiles with whole-frame identity,
ordering, duplicate/stale rejection, per-tile checksums, and a final frame
checksum while keeping the current BAR size.

**Pros:** Lowest shared-memory footprint; avoids larger BAR reservations; can
scale beyond 4K without a frame-sized arena.

**Cons:** Largest security/state-machine surface; checksum-first presentation
needs a hidden full frame or a second tile replay; more polls/copies and poor TCG
latency; timeout/recovery semantics become substantially harder.

**Effort:** XL, approximately 18–25 files.
