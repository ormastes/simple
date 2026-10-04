# RV64 static initial-exec TLS acceptance

Source: `test/03_system/app/compiler/feature/item4_riscv_tls_ie_spec.spl`.
Requirements: ITEM4-REQ-004, ITEM4-REQ-005, ITEM4-REQ-006.

Status: **UNRUN**. This is an authored manual, not generated execution evidence.
No admitted self-hosted Simple runtime is available. LLVM fixture generation
and independent ELF inspection succeeded; they do not establish Simple RED or GREEN.

| Scenario | Observable contract |
|---|---|
| Scanner unit prerequisite | Same key gets separate address/IE slots; repeated IE reuses its slot |
| Direct objects | Decode actual AUIPC/LD targets; inspect distinct TP-offset GOT slots and repeated-slot reuse |
| Archive provider | Real archive extraction produces the same initialized/zero TLS contract |
| Mixed ordinary/TLS GOT | Ordinary slot holds a virtual address; IE slots hold TP offsets |
| TLS alignment residue | Two text sizes exercise nonzero TLS-start residue with `.tdata` alignment 8 and `.tbss` alignment 64 |
| Undefined STT_NOTYPE | Winning STT_TLS definition supplies symbol type |
| Nonzero high/low addends | Named rejection before returning image bytes |
| Non-TLS winning definition | TLS reference cannot disguise an ordinary definition |
| Missing paired high | Named orphan-low rejection |

Eight full-link scenarios plus one scanner unit prerequisite include RISC-V ELF64 executable machine/type, output STT_TLS
offsets, PT_TLS alignment and extents, and exact initialized values 42/99.
Mutation helpers validate their fixture assumptions before modifying wire bytes.
The same-key scanner case is deliberately synthetic resolved input; it does not
claim ordinary GOT references to TLS symbols are ABI-admitted. The mixed binary
fixture uses an ordinary non-TLS symbol.

Once an admitted runtime exists, run from repository root:

```text
<runtime> test test/03_system/app/compiler/feature/item4_riscv_tls_ie_spec.spl --native
<runtime> spipe-docgen test/03_system/app/compiler/feature/item4_riscv_tls_ie_spec.spl --output doc/06_spec --no-index
```

This byte-returning API has no destination path, so these tests make no atomic
publication or sentinel-preservation claim. RV32, dynamic TLS, GD/TLSDESC,
instruction relaxation, host execution and threads remain open product gates.
