# Emu (Vt-physics) media backend truncates page word 0 to 8 bits

**Status:** OPEN
**Found:** 2026-09-01, while building `fw/nvme_multiblock_witness_check.spl`
**Scope:** `ftl_new_emu()` only. The behavioural backend (`ftl_new()`) is correct.

## Symptom

On the emu backend, word 0 of a `PageData` is masked to its low 8 bits on the
way through the media. Every other word round-trips intact.

```
# examples/09_embedded/simpleos_nvme_fw/fw/, page with words[0]=0x900,
# words[1]=0x901, words[511]=0x902, written and read back through Ftl:
behavioural: w0=2304 w1=2305 w511=2306      <- correct
emu:         w0=0    w1=2305 w511=2306      <- word 0 masked: 0x900 & 0xFF == 0
```

`0x900 -> 0`, `0x901 -> 1`, ... i.e. exactly `& 0xFF`, and *only* for index 0.

## Why this is not a payload-widening regression

Reproduced identically with `fw/nvme_types.spl`, `fw/nvme_qset.spl`,
`fw/nvme_controller.spl` and `fw/hil_command.spl` stashed back to their
pre-multi-block state. It is pre-existing and independent of that work.

It is invisible to the existing suite because `nvme_emu_media_check.spl` and
`nvme_emu_recovery_check.spl` both use byte-sized payload patterns (0x01,
0x5A, ...), which survive the mask unchanged; and
`payload_widening_witness_check.spl`, which does use large sentinels, runs on
the BEHAVIOURAL backend only.

## Suspected location

The word-0 path through `fw/fil_nand_emu.spl` / `fw/fil_fmc.spl` — the same
place the legacy `data: i64` one-byte payload stand-in used to live
(`prp_byte` returns `& 0xFF`). Not investigated further here: those files are
owned by another workstream and were not touched.

## Current mitigation

`fw/nvme_multiblock_witness_check.spl` section E (the emu-backed partial-failure
case) keeps its word-0 sentinels inside one byte and does its block
discrimination on words 1 / 255 / 511, which are unaffected. The workaround is
marked in that file so it is removed rather than forgotten when this is fixed.
