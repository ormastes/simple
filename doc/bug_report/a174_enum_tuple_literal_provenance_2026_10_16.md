# A174 inline tuple enum payload provenance (2026-10-16)

Bug database reconciliation pending. Producer A174 SHA256 a174b8e70b0a0ea4531db2ac5b8553f216590a7fbad0567cd9e40fd8e4630994 rejects WireCase.TupleOnly((7,9)) with payload type mismatch at0. Its declaration is TupleOnly(value: (i64,i64)). Direct native contract cycle1 passed51 HIR modules and traversed51 MIR modules before this semantic failure; no objects or executable resulted.

Evidence: phase3-validation-20261016/manual-enum-wire-contract-cycle1/command.txt and compile.log. The fixture source was committed as2b0fe4e6db0 and its frozen file digest remained unchanged. Native compilation was a direct command, with no outer build script.

The workaround explicitly binds the same tuple as (i64,i64) before passing it to the same constructor. Both tuple contents and the single-payload tuple roundtrip assertions remain unchanged. This preserves the intended test rather than dropping the rejected shape. The recovery reference identifies the exact original fixture; no compiler-owner repair is yet qualified. Actual workaround commit is recorded in the direct cycle2 evidence. Qualification is pending cycle2; this is a new runtime-boundary contract lane with at most3 attempts, not a reset of the exhausted earlier lanes.


## 2026-11-26 WA-P8 Audit & Resolution (`a174_enum_tuple_literal_provenance_2026_10_16`)

- **Disposition**: Retired (`@workaround` removed from `test/04_smoke/enum_wire_boundary_native.spl`).
- **Prior Stage2 & current verification**: Commit `0644f8f8a22` already verified `test/fixtures/native_stage2_workaround_shapes/enum_tuple_literal_payload.spl` (`W.TupleOnly((7, 9))`) passes natively on `stage2_new4`. Two-module lowering (`src/lib/nogc_sync_mut/sffi/enum_wire.spl` + `WireCase.TupleOnly((7, 9))` in `require_slot` and `enum_wire_restore_nil`) passes HIR, MIR, `mir_verify_module`, and `MirToLlvm` cleanly (`hir=0 mir=0 mirv=0 llvm=0 void=0`) with `rt_alloc` + `rt_enum_new`.
- **Changes made**:
  - Removed `# @workaround bug=a174_enum_tuple_literal_provenance_2026_10_16` and `val tuple_payload: (i64, i64) = (7, 9)` from `test/04_smoke/enum_wire_boundary_native.spl`, restoring direct inline `WireCase.TupleOnly((7, 9))` calls (recovering `2b0fe4e6db0` construct).
  - Verified (`--mode=interpreter`) via `test/01_unit/compiler/wa_p8_test_workarounds_spec.spl` (4/4 pass). `bug_db.sdn` was left untouched to preserve `.sdn` CRC32 seals.
