# Hosted ARM64 ADDEND acceptance

**UNRUN.** Five authored scenarios in
`test/03_system/app/compiler/feature/item4_macho_addend_spec.spl` trace
ITEM4-REQ-004/006. Initial intent `a1d863b52ea` plus real objects
`67f0ac9b319` preceded production edits. This is not an executed RED/GREEN claim.

| Scenario | Actual oracle |
|---|---|
| Signed local pairs | Real assembler object plus real definition object through `macho_hosted_link`; validate all twelve relocation records, decode ±branch targets and ADRP+ADD/scaledLDR effective addresses, inspect emitted DATA segment and77/88 markers. Negative24 payloads are guarded mutations. |
| Malformed pairs | Orphan prefix, extern/pcrel/width errors, mismatched address, unsupported follower, patch beyond section and overlapping consumed pairs return named errors. |
| Double-encoded addends | Nonzero explicit plus embedded B/BL, ADRP, ADD or LDR field rejects. |
| Zero explicit local pairs | Embedded branch/page/ADD/LDR addends still yield independent expected instruction words. |
| Imported branch policy | Real dylib provides `_helper`; zero explicit reaches actual emitted stub, positive/negative explicit or nonzero embedded branch addends reject. |

The public image builder returns bytes or an error and has no destination path;
these scenarios do **not** claim filesystem publication/sentinel coverage.
No GOT/TLV ADDEND follower support, Darwin execution, dyld loading or signing
admission is inferred. Object provenance and the external negative-literal
assembler limitation are recorded in `test/fixtures/linker/macho/ADDEND_PROVENANCE.md`.

After an admitted full CLI is available, set `SIMPLE_BINARY` to that exact
absolute producer and run from the checkout root:

```text
<admitted-runtime> test test/03_system/app/compiler/feature/item4_macho_addend_spec.spl --native-backend=llvm --sequential --no-cache --no-db --no-session-daemon --assert-ran --keep-artifacts --verbose
```

Require five executed scenarios with real assertions and no failures; preserve
producer/argv/results receipts. External assembly validation does not replace
Simple execution or the remaining full linker/five-host gates.
