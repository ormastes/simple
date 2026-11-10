# Emu (Vt-physics) media backend truncates page word 0 to 8 bits
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** FIXED — 2026-11-11 (lane ne18); the one-byte payload path was
replaced by the full-page seam (`41f9adb67f3c`, 2026-09-02), ancestor of
release/1.0.0 tip; word-0 round-trip re-proven on the emu backend below.
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

## Addendum 2026-11-11 (lane ne18) — FIXED, verified

Triage verdict: **FIXED** by the payload-widening work. The host write/read
path no longer touches the one-byte scalar seam:

- `Ftl.write_page` (`fw/ftl.spl:156`) now calls `fil.program_page(ppn, lba, s,
  data: PageData)`, and on the emu backend `NandEmu.program_page`
  (`fw/fil_nand_emu.spl:379`) drives ALL 4096 columns through the ONFI
  `data_in` handshake — no `& 0xFF` anywhere on this path. Reads return the
  full sensed page (`sense_page`, `fw/fil_nand_emu.spl:439`).
- The remaining `& 0xFF` sites (`fil_nand_emu.spl:358/367/374`, the
  `scalar_of_page`/`scalar_into_page` pair at `fw/fil_fmc.spl:204-216`,
  `fw/dram.spl:143-146`) are the deliberately-preserved SCALAR byte contract,
  now used only for RAIN parity word-0 bookkeeping, journal rebuilds and
  introspection — never for host page data.
- The `& 0xFF` merge in `scalar_into_page`/`fil_nand_emu.spl:374` preserves
  bytes 1..7 of word 0 on repair (it splices the low byte only), so even the
  legacy scalar repair path no longer wipes word 0.
- The payload widening reached the emu backend under commit `41f9adb67f3c`
  (2026-09-02, "feat(nvme): host-equivalent transport, registers, PRP, page
  ECC, profiles, offload"), an ancestor of the release/1.0.0 tip this lane was
  cut from; the companion witness
  `fw/emu_payload_widening_witness_check.spl` exists for non-vacuity.

Verification actually run in this lane (seed-smoke: fresh seed build-commit
46fe8f6b6def, `SIMPLE_LIB=src`, interpreter mode): a temporary probe (not
committed) wrote a page with `words[0]=0x900, words[1]=0x901, words[511]=0x902`
through `ftl_new_emu()` and read it back — all three words returned intact
(`word 0 (2304)`, `word 1 (2305)`, `word 511 (2306)`, probe verdict
"ROW2 WORD0 ROUND TRIP OK", exit 0; `SIMPLE_TIMEOUT_SECONDS=260`, ~130 s under
the interpreter). This is the bug doc's own reproducer value (0x900 masked to 0
pre-fix).

Follow-up for the owning nvme-fw lane (not done here): section E of
`nvme_multiblock_witness_check.spl` still carries the one-byte-sentinel
workaround (`val EB: i64 = 0x10`) and its now-stale "the emu backend truncates
page word 0" comment. The base override can be removed (e.g. back to a
multi-byte base) now that word 0 round-trips; the strengthened witness needs
`SIMPLE_TIMEOUT_SECONDS=0` and an interpreter budget far beyond this triage
lane's, so the cleanup is left to the lane that owns that file.

