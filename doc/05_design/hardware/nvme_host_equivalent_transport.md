# Host-equivalent NVMe transport (one test source, two substrates)

**Status:** emulator substrate implemented and green; board substrate declared and UNBOUND.
**Code:** `examples/09_embedded/simpleos_nvme_fw/fw/{nvme_mmio,nvme_transport_config,nvme_host_driver}.spl`
**Config:** `examples/09_embedded/simpleos_nvme_fw/fw/nvme_transport_profiles.sdn`
**Gate:** `bin/simple run examples/09_embedded/simpleos_nvme_fw/fw/host_equiv_transport_check.spl`
→ last line `HOST EQUIV TRANSPORT OK`. **Never assert on the exit code**
(`doc/08_tracking/bug/simple_run_exit_code_garbage_for_unit_main_2026-09-01.md`).

## 1. Problem

Tests called `c.process_one_io(cmd_make(...))` — a direct function call no real host
makes. `fw/hil_queue.spl` modelled the rings as *parallel struct-field arrays*
(`sq_cid`, `sq_op`, …), not as memory with a byte layout; there were no doorbell
registers, no phase tag and no MMIO path anywhere under `fw/`. So a test could not
be the same code a real host driver runs.

Requirement: **a test's source must be byte-identical between emulation and a real
board; only CONFIG differs.** Under emulation a write to queue memory or a doorbell
notifies the emulator; on hardware the identical write lands in BAR-mapped memory.

## 2. Memory model

One flat byte space (`[i64]`, one byte per element) owned by exactly one struct,
`HostNvme.mem`. Bases come from config, so the same code addresses an emulated
space or a real BAR/DRAM aperture.

| region | emu profile | meaning |
|---|---|---|
| SQ ring | `sq_base` 0, 64 × 64 B | host-written submission entries |
| CQ ring | `cq_base` 4096, 64 × 16 B | device-written completion entries |
| SQ0TDBL | `doorbell_base` 8192 | submission tail doorbell |
| CQ0HDBL | `doorbell_base + doorbell_stride` | completion head doorbell |

Doorbell placement follows NVMe: `SQyTDBL = base + (2y)·stride`,
`CQyHDBL = base + (2y+1)·stride`. Only queue 0 is wired today.

### Real NVMe field offsets (`nvme_mmio.spl`)

SQE, 64 bytes:

| off | field |
|---|---|
| +0 | CDW0 — opcode[7:0], **CID[31:16]** |
| +4 | NSID |
| +24 | PRP1 (64-bit) |
| +40 | CDW10/11 = SLBA (64-bit) |
| +48 | CDW12 — NLB[15:0] |

CQE, 16 bytes:

| off | field |
|---|---|
| +0 | DW0 command-specific result |
| +8 | DW2 — SQHD[15:0], SQID[31:16] |
| +12 | DW3 — **CID[15:0], PHASE bit 16, STATUS[31:17]** |

All accessors are little-endian and fail closed (out-of-range read → 0, out-of-range
write → dropped).

## 3. Protocol

```
host                          memory                        device
submit_sqe(cmd)      --->  SQ[tail] = 64 bytes
                            (device has NOT seen it yet)
ring_sq_doorbell()   --->  MMIO[SQ0TDBL] = tail   ------->  fetch SQE(s), execute
poll_cq()            <---  CQ[head].DW3 phase bit <-------  write CQE, toggle phase on wrap
  (on match)         --->  MMIO[CQ0HDBL] = head
```

**The doorbell write is the notification.** Nothing else crosses the seam. Section C
of the check proves this: after `submit_sqe` the device's serviced counter is still
0 and `cq_ready()` is false; it is the doorbell write that makes the device fetch.

**Phase tag.** Host starts expecting phase 1 (CQ memory is zeroed, so an unwritten
entry reads phase 0 and is correctly refused). The device writes its own phase and
toggles on CQ-tail wrap; the host toggles its expected phase on CQ-head wrap. A CQE
whose phase bit does not match the expectation is **not consumed** and head does not
advance — the classic real-driver bug, tested directly in sections F and G.

## 4. The config seam

`nvme_transport_profiles.sdn` (SDN, ASCII, read relative to the repo root) declares
named profiles. `transport_profile_load(name)` returns a `TransportProfile`, or a
`valid == 0` profile if the name is absent or any of the 9 fields is
missing/non-numeric — fail closed, never a silently-defaulted profile.

`HostNvme.cfg.backend` is the only thing that decides what a doorbell write *means*:

- `emu` — bound. `ring_sq_doorbell()` calls `device_service()`, which fetches SQEs
  out of `mem`, decodes them with `sqe_decode`, drives the existing firmware (`Hil`),
  and writes phase-tagged CQEs back into `mem`.
- `board` — declared, **not bound**. `attach()` returns false and `attach_reason()`
  says why. Nothing fakes a second substrate.

The shared submission path is `HostNvme.exec_io(cmd)` — one `me` method, called
identically by the emu section and the board section of the check. Binding a board
means adding a branch in `ring_sq_doorbell`/`poke` that targets real MMIO, and
flipping `bound: 1` in the SDN. **No test source changes.**

`exec_io` is a `me` method, not a free function taking `HostNvme`: Simple values are
copied by value, so a free function would mutate a copy and lose queue state.

## 5. What is genuine vs. narrowed

**Genuine NVMe semantics:** 64-byte SQE / 16-byte CQE at the real offsets; CID in
CDW0[31:16] and CQE DW3[15:0]; status in DW3[31:17]; phase bit 16 with wrap toggle
on both sides; SQHD in DW2; little-endian; tail/head doorbell registers at NVMe
stride; fail-closed bounds on every access.

**Narrowed, and named as such:**
- **Payload.** The host command payload is still the one-word `NvmeCmd.data`
  (payload plan D4/D5 not done). It is carried in the **PRP1** field, so the SQE
  shape is right, but PRP1 is *carried, not honored* — there is no PRP list walk and
  no data buffer in memory. Real payload DMA is the next slice.
- **Single queue pair.** Only SQ0/CQ0. Admin queues (ASQ/ACQ/AQA) and multiple I/O
  queue pairs are not wired.
- **No controller registers.** CAP/VS/CC/CSTS and the enable handshake are not in
  this aperture; `attach()` stands in for controller enable.
- **No interrupts.** Completion discovery is polling only (which is legitimate NVMe,
  but MSI-X is absent).
- **Synchronous device.** The emu backend services the queue inline on the doorbell
  write, so there is no genuine concurrency window between doorbell and completion.
- **`hil_queue.spl` is untouched.** Per the hardening plan's migration rule the new
  modules WRAP it: `device_service` drives `Hil`, which owns the old parallel-array
  rings. The memory-mapped rings and the legacy rings coexist; migrating the
  firmware side onto memory rings is a later vertical slice.

## 6. Value-semantics note

`HostNvme` is the single owner of `mem`. Every write is `me.mem[i] = v`; there is no
`val t = me.mem; t[i] = …` anywhere, which under copy-on-write would deep-copy the
whole ring per byte in the submit hot path. All read-side helpers in `nvme_mmio.spl`
are free functions that take `mem` and never mutate, so passing it is a cheap COW read.
