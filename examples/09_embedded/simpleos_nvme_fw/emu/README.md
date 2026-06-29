# Pure-Simple NVMe host/device emulator (custom-typed, ONFI NAND, Lean4-verified)

A pure-Simple NVMe SSD **emulator** split into a **host interface** and a **device
interface** that exchange data only across a **settable memcpy/DMA seam**, backed by
an **ONFI** NAND model (RAM-backed) and a compact FTL, with the core invariants
**proven in Lean4**. No C anywhere. Gate: `bin/simple run` (not `check`).

```
 HOST INTERFACE            SEAM (RAM-backed shared mem)          DEVICE INTERFACE
 host_write/read  --host memcpy-->  SharedMem  <--dev memcpy--   dev_step
 host_fetch_data                  (data buffers)                 FTL -> ONFI NandArray
        \____________________ NvmeEmu owns shared + ftl + nand + both ports ____________/
```

## Geometry
2 channels × 2 banks × 2 planes × 2 blocks × 8 pages = **128 physical pages**, 96
surfaced LBAs, 4 i64 words/page. `ppn = ((((ch*2+bank)*2+plane)*2+block)*8+page)`.

## Modules
| file | role |
|------|------|
| `nvme_ct.spl` | locked interface: domain **newtypes** (Lba/Ppn/Ch/Bank/Plane/Block/Page/Cid/Qid/Addr), geometry, address codec, Command/Completion |
| `nand_onfi.spl` | `NandArray` — ONFI command/address/data handshake per channel, RAM-backed media, OOB, bad-block + fault injection |
| `nvme_shared.spl` | `SharedMem` — the RAM-backed DMA region (owned-field store/load) |
| `nvme_memcpy.spl` | `Dma` — the **settable** memcpy seam (`set_copy`, default + fault-injecting copies) |
| `ftl_emu.spl` | compact L2P FTL over the NAND (log append; no GC — minimal by design) |
| `nvme_host.spl` / `nvme_device.spl` | `HostPort`/`DevPort` + the `NvmeEmu` owner struct: host & device interfaces |
| `nvme_emu_main.spl` | end-to-end demo + the memcpy-seam fault-injection proof |
| `proofs/*.lean` | Lean4: `Addr` (bijection/bounds), `Memcpy` (length safety), `Queue` (ring invariants), `Resource` (region disjointness, use-after-free) |

## Run
```bash
bin/simple run examples/09_embedded/simpleos_nvme_fw/emu/nvme_emu_main.spl   # -> EMU E2E PASS
# self-tests: nand_array_selftest + shared_memcpy_selftest + ftl_selftest + nvme_device_selftest (116 asserts)
export PATH="$HOME/.elan/bin:$PATH"
for f in Addr Memcpy Queue Resource; do lean examples/09_embedded/simpleos_nvme_fw/emu/proofs/$f.lean; done  # exit 0, no sorry
```

## "Highly custom typed" — honest scope
Domain **newtypes** are used pervasively in signatures/records. On this compiler they
are **not enforced** (a `Ppn` is accepted where an `Lba` is expected) and arithmetic
erases the wrapper — see `doc/08_tracking/bug/newtype_run_path_and_enforcement_gaps_2026-06-29.md`.
So the types document intent; the **enforced** guarantees (address bijection, memcpy
bounds, queue invariants, resource safety) are the **Lean4 proofs**. The seam carries
data only via the settable memcpy on *both* sides — proven by injecting a faulting
memcpy on each side and observing the corrupted byte.
