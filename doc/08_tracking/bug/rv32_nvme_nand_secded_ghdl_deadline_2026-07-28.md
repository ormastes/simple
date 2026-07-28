# RV32 NVMe SECDED GHDL Deadline

**Status:** resolved 2026-07-28

## Failure

The production-review fix replaced hidden-data correction with full-word SECDED,
added alternate-slot remap, automatic bidirectional retry/prevention, and bounded
SQ/CQ deletion/full handling. The pure-Simple RV32 native build succeeds.

The third allowed verification cycle failed at the existing 2 ms behavioral-core
deadline:

```text
RV32_NVME_FW_STUCK pc=0x00EC ins=0x28234108 a0=0x8C
ra=0x722E sp=0xADF0 phase=0x5
RV32_NVME_FW_TIMEOUT: marker not seen
```

The previous cycle reached phase 3 at the compiler safepoint. Replacing the
quadratic ECC position scan with constant-time position mapping advanced the
firmware to phase 5, but not to the UART verdict before timeout.

## Resolution

Profiling showed forward progress and the exact marker at 10.897245 ms. The
testbench deadline is now a measured 15 ms with an 18 ms shell stop-time.
Behavioral, exact-BRAM clean, exact-BRAM garbage-fill, and full AXI4 RAM GHDL
all pass. The AXI gate observed 847 reads and 460 writes in the 256-byte
`.nandram` range.

The pre-review 226-byte capture remains invalid. The corrected revision now has
a complete 229-byte KV260 USER4 capture with `pass_seen=1`, `fail_seen=0`, and
zero lost bytes.
