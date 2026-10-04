# Hosted ARM64 ADDEND acceptance

**UNRUN.** Eight authored scenarios in
`test/03_system/app/compiler/feature/item4_macho_addend_spec.spl` trace
ITEM4-REQ-004/006. Initial intent `a1d863b52ea` plus real objects
`67f0ac9b319` preceded production edits. This is not an executed RED/GREEN claim.

| Scenario | Actual oracle |
|---|---|
| Signed local pairs | Real assembler object plus real definition object through `macho_hosted_link`; validate all twelve relocation records, decode ±branch targets and ADRP+ADD/scaledLDR effective addresses, inspect emitted DATA segment and77/88 markers. Negative24 payloads are guarded mutations. |
| Malformed pairs | Orphan prefix, extern/pcrel/width errors, mismatched address, unsupported follower, patch beyond section and overlapping consumed pairs return named errors. |
| Double-encoded addends | Nonzero explicit plus embedded B/BL, ADRP, ADD or LDR field rejects in hosted and static linkers. |
| Zero explicit local pairs | Embedded branch/page/ADD/LDR addends still yield independent expected instruction words through both linkers. |
| Imported branch policy | Real dylib provides `_helper`; zero explicit reaches actual emitted stub, positive/negative explicit or nonzero embedded branch addends reject. |
| Decoder boundaries | Signed24 zero/max/min/-1; ordinary ARM64 and x64 consume one, paired ARM64 consumes two, invalid indices reject with input identity. |
| Real file publication refusal | Native Mach-O adapter reads task-owned malformed object and real provider, rejects ADDEND, and preserves an existing destination sentinel. |
| Subtractor compatibility | Actual assembler-produced subtractor/unsigned pair remains0x5000 through hosted and static images, checked against distinct text/data markers. |

The destination scenario uses the real file adapter and publisher boundary;
the other image cases use the public byte-oriented builder.
No GOT/TLV ADDEND follower support, Darwin execution, dyld loading or signing
admission is inferred. Object provenance and the external negative-literal
assembler limitation are recorded in `test/fixtures/linker/macho/ADDEND_PROVENANCE.md`.

After an admitted full CLI is available, set `SIMPLE_BINARY` to that exact
absolute producer and run from the checkout root:

```text
<admitted-runtime> test test/03_system/app/compiler/feature/item4_macho_addend_spec.spl --native-backend=llvm --sequential --no-cache --no-db --no-session-daemon --assert-ran --keep-artifacts --verbose
```

Require eight executed scenarios with real assertions and no failures; preserve
producer/argv/results receipts. External assembly validation does not replace
Simple execution or the remaining full linker/five-host gates.
