# Shadow Doorbell Host-Controller Notes (Mode 6)

> Quick crib sheet for implementing a host/virtual NVMe controller that honors the Doorbell Buffer Config command and mirrors shadow doorbell changes into MMIO doorbells when hardware polling is absent.

## MMIO + Identify essentials
- CAP.DSTRD defines doorbell stride: `stride_bytes = 4 << DSTRD`.
- Doorbell registers stay at `0x1000 + (2*qid + is_cq) * stride_bytes`.
- Identify Controller must advertise OACS bit 8 = 1 to expose the Doorbell Buffer Config (DBBUF) admin command.

## Driver sequence (guest view)
1. Map BAR, read CAP/VS.
2. Program AQA/ASQ/ACQ while CC.EN=0.
3. Set CC.MPS/IOSQES/IOCQES, then CC.EN=1 and wait for CSTS.RDY=1.
4. Issue Identify Controller → sees OACS.bit8 set.
5. Allocate two page-aligned buffers (page size from CC.MPS): shadow DB + EventIdx.
6. Send admin opcode 0x7C with PRP1=shadow, PRP2=eventidx. After success, host writes doorbells via shadow buffer.

## Controller behavior (what we emulate)
- Track `shadow_db_pa`, `eventidx_pa`, `dbbuf_enabled`. Clear on CC.EN 1→0.
- On receiving opcode 0x7C:
  - Validate alignment vs CC.MPS and size vs stride/queue count.
  - Map both buffers, mark `dbbuf_enabled=true`.
  - Optionally seed EventIdx entries to current doorbell values.

## Polling/notification model
- Shadow buffer layout mirrors MMIO: `SQy` at `(2*y)*stride`, `CQy` at `(2*y+1)*stride`.
- Hardware-perfect path: controller DMA-polls shadow buffer and updates EventIdx; MMIO is optional.
- Software assist path (what Mode 6 uses on PM9A1 when firmware hides bit 8):
  - CPU thread polls shadow buffer, rings real MMIO doorbells on change.
  - EventIdx can be updated the same way if desired.

## Reset rules
- DBBUF state does **not** survive controller reset. On CC.EN=0 or FLR:
  - Clear stored PRPs and `dbbuf_enabled`.
  - Stop any software mirror threads.

## Useful offsets
- SQ Tail doorbell offset: `(2*qid) * stride_bytes`
- CQ Head doorbell offset: `(2*qid + 1) * stride_bytes`

Keep the above handy when wiring up the host-controller daemon or virtual device so Mode 6 can see shadow-doorbell activity even when hardware polling is missing.
