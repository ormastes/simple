# riscv_compressed specs red: decode regressions suspected (2026-09-16)

## Observed
- `test/01_unit/lib/hardware/riscv_common/riscv_compressed_zca_seed_spec.spl`:
  1 failure — `expected 4269331 to equal 4269315` (re-encoded parcel differs
  from expected by 16; off-by-one in an immediate/offset field suspected).
- `test/01_unit/lib/hardware/riscv_common/riscv_compressed_mission_critical_spec.spl`:
  4 failures — `expected false to equal true` and
  `expected <empty> to equal C.ADDI16SP` (decoder returns empty text for a
  mnemonic it should resolve).

## Impact
ZCA seed encode parity and mission-critical mnemonic coverage are dark; the
empty-mnemonic result looks like a real decoder gap, not a stale expectation.

## Expectation
Decoder round-trips the pinned fixtures; failing to decode C.ADDI16SP on the
mission-critical path is a defect in `src/lib/hardware/riscv_common` decode
tables.

## Unblock condition
Root-cause the +16 delta and the empty mnemonic; fix decoder or, if a fixture
constant was deliberately changed, update the spec with the deciding commit.
