<!-- GENERATED — DO NOT EDIT. -->
<!-- Regenerate: `bin/simple spipe-docgen --audience=qa test/03_system/app/nvme_firmware/nvme_rv32_wire_spec.spl` -->

# NVMe RV32 Firmware — Wire-Level Verification Manual

> Every table in this manual was captured from a verified test run on 2026-07-05.
> Bit-level captures compare the live device/wire bytes against the declared frame
> layout and cannot drift from the firmware. Verification record: Appendix A.

Bit-table captures render the **same bytes at a declared alignment** so a reviewer
can read fields at the granularity they matter: 32-bit for dwords, per-bit for a
control register, 8/16-bit for a packed wire frame. The `view:` selector controls
the column stride. Mismatched rows show hex **and** binary so the offending bit is
visible; masked fields (volatile ids, timestamps) are compared as `··` and never
fail the run.

---

## Scenario A — NVMe CQ completion entry check

Booted the rv32 kernel on QEMU, issued one admin Identify command, and captured the
16-byte Completion Queue Entry the controller wrote back. The layout is four dwords;
the phase bit in DW3 must equal the CQ's current phase tag, or the driver would
consume a stale entry.

**Steps**
1. Ring the SQ tail doorbell for the Identify command.
2. Poll the CQ head until the phase bit flips; capture the 16-byte entry.
3. Compare the entry against the `nvme_cqe` frame layout (`view: bits32`).

Capture `cqe_identify` — `view: bits32`, aligned to 32-bit dwords:

| Offset | Bits    | Field                | Expected              | Actual                | Match |
|--------|---------|----------------------|-----------------------|-----------------------|-------|
| 0x00   | [31:0]  | DW0 Command Specific | `0x00000001`          | `0x00000001`          | ✅    |
| 0x04   | [31:0]  | DW1 Reserved         | `0x00000000`          | `0x00000000`          | ✅    |
| 0x08   | [15:0]  | SQ Head Pointer      | `0x0003`              | `0x0003`              | ✅    |
| 0x08   | [31:16] | SQ Identifier        | `0x0000`              | `0x0000`              | ✅    |
| 0x0C   | [15:0]  | Command Identifier   | `····` (masked)       | `0x0041`              | ➖    |
| 0x0C   | [16]    | Phase bit (P)        | `1` `0b1`             | `0` `0b0`             | ❌    |
| 0x0C   | [31:17] | Status Field (SC/SCT)| `0x0000`              | `0x0000`              | ✅    |

The phase-bit row failed: the CQ round had toggled to phase `1`, but the captured
entry still carried the previous round's `0` — a stale completion. Command
Identifier is masked (`····`) because it is allocated per-submission and is not
byte-stable across runs; it renders for context but never gates the comparison.

---

## Scenario B — Controller Configuration register (CC) bit-field check

Read the 32-bit `CC` (Controller Configuration) MMIO register after enable and
checked each control field. A single 32-bit word is best read per-field, so the
capture uses `[31:24]`-style bit ranges.

**Steps**
1. Write the enable sequence, then read back `CC` at `BAR0 + 0x14`.
2. Compare against the `nvme_cc` bit-field layout (`view: bits32`, field ranges).

Capture `cc_after_enable` — one 32-bit register, field-range view:

| Offset | Bits    | Field                 | Expected   | Actual     | Match |
|--------|---------|-----------------------|------------|------------|-------|
| 0x14   | [0]     | EN (Enable)           | `1`        | `1`        | ✅    |
| 0x14   | [3:1]   | Reserved              | `0b000`    | `0b000`    | ✅    |
| 0x14   | [6:4]   | CSS (Command Set)     | `0b000`    | `0b000`    | ✅    |
| 0x14   | [10:7]  | MPS (Mem Page Size)   | `0b0000`   | `0b0000`   | ✅    |
| 0x14   | [13:11] | AMS (Arbitration)     | `0b000`    | `0b000`    | ✅    |
| 0x14   | [15:14] | SHN (Shutdown Notif)  | `0b00`     | `0b00`     | ✅    |
| 0x14   | [19:16] | IOSQES (SQ entry sz)  | `0x6`      | `0x6`      | ✅    |
| 0x14   | [23:20] | IOCQES (CQ entry sz)  | `0x4`      | `0x4`      | ✅    |
| 0x14   | [31:24] | Reserved              | `0x00`     | `0x00`     | ✅    |

All fields matched: the controller came up with 64-byte SQ entries (`IOSQES=6`,
2^6) and 16-byte CQ entries (`IOCQES=4`, 2^4), enable asserted, no shutdown pending.

---

## Scenario C — NVMe/TCP capsule PDU wire frame (multi-alignment view)

Captured the first 8 bytes of a Command Capsule PDU off the wire and rendered the
same bytes at 8-bit and 16-bit alignment. The 8-bit view reads the packed header
byte-by-byte; the 16-bit view reads the little-endian length fields as halfwords.

**Steps**
1. Sniff the outbound PDU header before the SQE payload.
2. Compare the byte stream against `nvmet_pdu` at `view: bits8`, then `view: bits16`.

Capture `capsule_pdu` — `view: bits8`, aligned to bytes:

| Offset | Bits   | Field              | Expected  | Actual    | Match |
|--------|--------|--------------------|-----------|-----------|-------|
| 0x00   | [7:0]  | PDU-Type           | `0x04`    | `0x04`    | ✅    |
| 0x01   | [7:0]  | FLAGS              | `0x00`    | `0x00`    | ✅    |
| 0x02   | [7:0]  | HLEN               | `0x48`    | `0x48`    | ✅    |
| 0x03   | [7:0]  | PDO                | `0x18`    | `0x18`    | ✅    |
| 0x04   | [7:0]  | PLEN byte 0        | `0x48`    | `0x48`    | ✅    |
| 0x05   | [7:0]  | PLEN byte 1        | `0x00`    | `0x00`    | ✅    |
| 0x06   | [7:0]  | PLEN byte 2        | `0x00`    | `0x00`    | ✅    |
| 0x07   | [7:0]  | PLEN byte 3        | `0x00`    | `0x00`    | ✅    |

Same bytes, `view: bits16`, aligned to little-endian halfwords:

| Offset | Bits    | Field            | Expected   | Actual     | Match |
|--------|---------|------------------|------------|------------|-------|
| 0x00   | [15:0]  | Type/Flags       | `0x0004`   | `0x0004`   | ✅    |
| 0x02   | [15:0]  | HLEN/PDO         | `0x1848`   | `0x1848`   | ✅    |
| 0x04   | [15:0]  | PLEN low         | `0x0048`   | `0x0048`   | ✅    |
| 0x06   | [15:0]  | PLEN high        | `0x0000`   | `0x0000`   | ✅    |

Both views agree; the 16-bit view confirms `PLEN = 0x00000048` (72 bytes) reads
correctly as little-endian halfwords.

---

## Aligned-view switch — one word, three granularities

Scenario A's DW3 (offset `0x0C`, the word holding the phase bit) rendered at each
`view:` setting. This is how the `view: bits8|bits16|bits32` selector reshapes a
single 32-bit value — the bytes are identical, only the column stride changes.

Raw value: `0x00 00 00 41` (little-endian on the wire: `41 00 00 00`).

| view      | Columns                                   | Rendering                          |
|-----------|-------------------------------------------|------------------------------------|
| `bits8`   | 4 bytes, `[7:0]` each                     | `0x41` `0x00` `0x00` `0x00`        |
| `bits16`  | 2 halfwords, `[15:0]` each                | `0x0041` `0x0000`                  |
| `bits32`  | 1 dword, split by declared field ranges   | CID=`0x0041` P=`0` Status=`0x0000` |

The phase bit is only nameable at `bits32`, where the frame layout maps `[16]` to
field `P`. At `bits8`/`bits16` it reads as raw magnitude — useful for a hexdump
sanity check, useless for asserting the control bit. Pick the coarsest view that
still isolates the field you assert.

---

## Appendix A — Verification Record

This manual was generated by `bin/simple spipe-docgen --audience=qa` from
`test/03_system/app/nvme_firmware/nvme_rv32_wire_spec.spl`. All captures are live
device/wire bytes compared byte-wise against declared frame layouts.

| Scenario | Capture           | Layout       | View          | Result | Golden               |
|----------|-------------------|--------------|---------------|--------|----------------------|
| A        | `cqe_identify`    | `nvme_cqe`   | bits32        | ❌     | `cqe_identify.sdn`   |
| B        | `cc_after_enable` | `nvme_cc`    | bits32        | ✅     | `cc_after_enable.sdn`|
| C        | `capsule_pdu`     | `nvmet_pdu`  | bits8, bits16 | ✅     | `capsule_pdu.sdn`    |

Scenario A is a **recorded failure** capture: the phase-bit mismatch is the golden
expectation for the stale-completion regression test (`#NVME-RV32BOOT-001`), which
asserts the driver rejects an entry whose phase does not match the CQ round tag.
Masked fields (`····`): Command Identifier (Scenario A, `[0x0C][15:0]`) — allocated
per-submission, excluded from the byte-wise compare.
