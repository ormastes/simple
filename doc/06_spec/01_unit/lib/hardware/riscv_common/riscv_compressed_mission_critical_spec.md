# Mission-Critical RISC-V Compressed Subset Specification

> Executable source:
> `test/01_unit/lib/hardware/riscv_common/riscv_compressed_mission_critical_spec.spl`

This manual records the executable boundary for the mission-critical common
Zca compressed-instruction subset. It is deliberately narrower than either
the RV32 or RV64 compressed decoders: it recognizes only verified,
XLEN-independent common rows and makes no claim that the complete Zca
extension is implemented or release-qualified.

| Tests | Active | Skipped | Pending |
|------:|-------:|--------:|--------:|
| 9 | 9 | 0 | 0 |

## Boundary and claims

The manifest identifies the subset as `zca-common-integer-v1` under the `Zca`
name, but it does **not** advertise that extension. Legacy fallback is
forbidden. Exhaustive classification, target-RTL equivalence, and complete
per-row target evidence remain required but are not yet verified; therefore
the subset is not release-claimable.

The capability catalog contains 25 eligible common-Zca rows. Each row has a
`zca.c.` identifier, and the target-RTL evidence catalog has the same 25
entries. Evidence is tied to an explicit strict contract, including the
C.ADD, C.ADDI16SP, C.LUI, C.J, C.BEQZ, and C.BNEZ paths. The strict-contract
catalog is the common source for both lowering and capability evidence.

## Result contract

Every 16-bit parcel receives a deterministic, fixed-width hardware result:

- `original_parcel` is retained;
- `length_bytes` is always `2`;
- a legal result has a nonzero canonical instruction and reason code
  `COMPRESSED_REASON_NONE`;
- an illegal result has canonical instruction `0` and a distinct reason code.

The tested illegal classes are zero/reserved-zero,
`COMPRESSED_REASON_NOT_COMPRESSED`,
`COMPRESSED_REASON_RESERVED_ENCODING`, and
`COMPRESSED_REASON_UNSUPPORTED_ZCA_SEED`. This is a classification interface,
not an attempt to decode an unsupported parcel using a legacy decoder.

## Scenarios

### Refuses full-Zca advertising before proof obligations complete

1. Create the common-Zca mission-critical manifest.
2. Require the subset identifier and extension label to be stable.
3. Require advertising and legacy fallback to be disabled.
4. Require incomplete exhaustive-classification, RTL-equivalence, and
   per-row-evidence obligations to prevent a release claim.

### Uses one declarative table for common capabilities

1. Load the critical-subset capability entries.
2. Require exactly 25 entries.
3. Require every entry to be Zca, critical-subset eligible, and named
   `zca.c.*`.

### Derives target-RTL truth from explicit evidence

1. Load the target-RTL evidence catalog.
2. Require exactly 25 entries and a nonempty strict contract for each.
3. Require evidence entries to exist in both the critical-subset and target
   evidence lookups.
4. Require the named common rows and their RTL contracts to be present.

### Shares strict contracts between lowering and evidence

1. Load the strict-contract catalog.
2. Require more than 19 contracts.
3. Check the labels and ISA identifiers for C.ADD, C.BEQZ, C.BNEZ, and
   C.ADDI16SP.
4. Require every contract to identify a nonempty `zca.c.*` ISA row and label.

### Accepts only verified common rows

1. Expand a verified C.EBREAK parcel through RV32 and a verified C.ADDI parcel
   through RV64.
2. Require their expected legal canonical instructions.
3. Present parcel `0x2085`, whose Q1/funct3=001 meaning diverges between
   RV32 C.JAL and RV64 C.ADDIW.
4. Require both mission-critical decoders to reject it instead of invoking a
   legacy fallback.

### Preserves reason codes without illegal payloads

1. Classify zero, an uncompressed word prefix, a reserved encoding, and the
   RV32/RV64-divergent parcel.
2. Require every result to retain 2-byte width.
3. Require illegal results to carry canonical instruction `0`.
4. Require the distinct reason codes reserved-zero, not-compressed,
   reserved-encoding, and unsupported-Zca-seed respectively.

### Keeps claims narrower than per-XLEN decoder support

1. Inspect RV32 and RV64 integer capability tables.
2. Require C.JAL only in RV32 and C.ADDIW only in RV64.
3. Require neither row in the common critical subset.
4. Require the common manifest to remain non-advertising and
   non-release-claimable.

### Passes through an uncompressed RV64 instruction

1. Pass RV64 word `0x00100013` to the RV64 mission-critical expansion path.
2. Require it to remain legal and uncompressed with the same instruction word.
3. Do not treat this pass-through as Zca support or as an extension claim.

### Exhaustively classifies all 16-bit parcels deterministically

1. Iterate every parcel from `0` through `65535`.
2. Expand each parcel twice.
3. Require equal original parcel, canonical instruction, legality, and reason
   code across both results.
4. Require the fixed 2-byte result width for every parcel, `NONE` only for
   legal results, and a zero canonical instruction for every illegal result.

## Nonqualified scope

This specification does not qualify full Zca, RV32 C.JAL, RV64 C.ADDIW, a
legacy fallback path, complete target-RTL equivalence, or a production/release
capability advertisement. Its evidence is limited to deterministic fixed-width
classification and the explicit, verified common-row boundary above.
