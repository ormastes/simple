# A174 inline tuple enum payload provenance (2026-10-16)

Bug database reconciliation pending. Producer A174 SHA256 a174b8e70b0a0ea4531db2ac5b8553f216590a7fbad0567cd9e40fd8e4630994 rejects WireCase.TupleOnly((7,9)) with payload type mismatch at0. Its declaration is TupleOnly(value: (i64,i64)). Direct native contract cycle1 passed51 HIR modules and traversed51 MIR modules before this semantic failure; no objects or executable resulted.

Evidence: phase3-validation-20261016/manual-enum-wire-contract-cycle1/command.txt and compile.log. The fixture source was committed as2b0fe4e6db0 and its frozen file digest remained unchanged. Native compilation was a direct command, with no outer build script.

The workaround explicitly binds the same tuple as (i64,i64) before passing it to the same constructor. Both tuple contents and the single-payload tuple roundtrip assertions remain unchanged. This preserves the intended test rather than dropping the rejected shape. The recovery reference identifies the exact original fixture; no compiler-owner repair is yet qualified. Actual workaround commit is recorded in the direct cycle2 evidence. Qualification is pending cycle2; this is a new runtime-boundary contract lane with at most3 attempts, not a reset of the exhausted earlier lanes.
