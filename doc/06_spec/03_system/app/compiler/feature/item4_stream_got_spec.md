# Streamed static x64 GOT acceptance

Source: `test/03_system/app/compiler/feature/item4_stream_got_spec.spl`.
Requirements: ITEM4-REQ-004 and ITEM4-REQ-009.
Status: **UNRUN**. Authored manual; no admitted Simple RED/GREEN evidence.

| Scenario | Independent observation |
|---|---|
| Narrow windows | Real 9/41/42 instructions retain opcodes; displacement leads to RW slot then actual data/function; windows 1/3/8/64 yield identical images |
| Full family and identity | All 12 types; same-name locals separated by owner, equal-address globals distinct, repeated addends reuse slots, weak zero, common and archive targets |
| Inactive/base-only | No demand, unused anchor and nonallocated relocation leave exact unaligned cap unchanged; active zero-slot anchor/base adds padding without a reserved entry |
| Malformed requests | Invalid symbol, past-section patch, signed displacement overflow and unsupported TLS preserve destination sentinel |
| Reserved anchor | GLOBAL/WEAK definitions reject; actual LOCAL reference of the same spelling remains ordinary |
| Quotas/cancellation | Real opened GOT scan rejects exhausted allowance/cancellation; full-link GOT-only extent, scratch, scan and cancellation failures preserve sentinel |

The full family includes 3/9/25/26/27/28/29/30/31/41/42/43. Program headers
translate actual file/virtual addresses; no stream symbol table is assumed.
The seven streamed identities must occupy exactly 56 bytes in first-reference
order. GOT32 and 64-bit offsets are decoded as signed where appropriate.
Fast output uses semantic checks and may relax instructions; it is not required
to preserve stream layout or instruction bytes.

Fixture source and reproduction working directory:

```sh
cd test/fixtures/linker/elf
clang --target=x86_64-unknown-linux-gnu -c stream_got_*.s
llvm-ar rcs stream_got_provider.a stream_got_provider.o
llvm-readelf -r stream_got_families.o
llvm-objdump -d stream_got_families.o
```

LLVM 21 fixture inspection confirmed all relocation tags/addends and genuine
APX `movq ...,%r16` bytes `d5 48 8b 05` with relocation 43. Explicit `.reloc`
records supply assembler forms unavailable through LLVM suffix syntax. Bare
`.include` paths require the working directory shown above. Fixture assembly
and inspection ran; generated images and Simple specs did not.

After runtime admission:

```text
<runtime> test test/03_system/app/compiler/feature/item4_stream_got_spec.spl --native
<runtime> spipe-docgen test/03_system/app/compiler/feature/item4_stream_got_spec.spl --output doc/06_spec --no-index
```

Secure task-specific output directories must become removable after cleanup.
Logical quotas are not measured RSS, allocator overhead or complete bounded
admission. Dynamic GOT/PLT, TLS, host execution, other architectures and overall
item 4 readiness remain separate gates.
