# Streamed x86-64 ordinary GOT

Status: design and external ABI research; Simple execution UNRUN. This extends
the retained static ELF stream path under ITEM4-REQ-003/004/009. It does not
admit a production memory budget, dynamic linking, TLS, IFUNC, or runtime readiness.

## Ownership and base

Owner/session: `/root/linker_research`, `item4-stream-got-docs-20261004`.
Worktree: `C:/dev/simple-item4-stream-got-docs-20261004`.
Branch: `work/item4-stream-got-docs-20261004`.
Target: `origin/release/1.0`; inspection base and expected target:
`11a5ade180d895de65342ed983ce34ad06506a33` (fetched and checked).
Owned artifact: this document. Root owns integration; runtime owns production;
acceptance owns executable specs/manuals. Sidecars: N/A. No push or merge here.

## Local evidence and integration

`src/compiler/70.backend/linker/elf/stream_emit.spl` currently accepts scalar
relocations, supplies a symbol address to `reloc_apply_x86_64`, and rejects GOT
forms. Merely adding widths would mislink: the first argument must sometimes be
a slot address, slot offset, or GOT base instead of the symbol address.

`elf/stream_layout.spl` lays out regular sections and then canonical COMMON
storage in the writable segment. `stream_inputs.spl` owns charged symbol lookup
and archive closure. Their mutable-owner APIs must remain explicit. The existing
file transaction and retained input identity checks remain in force.

The resident fast driver `elf/elf_static_link.spl` and `elf/reloc_scan.spl` already
distinguish slot, base, and symbol-minus-base forms. Defined static PLTOFF64 uses
the resolved symbol; imported PLTOFF64 can instead use a PLT and is outside this
stream scope. The existing `reloc_engine.spl` remains the scalar arithmetic owner.
Public `elf_stream_link_file_v1` and its limits remain unchanged. Internal helper
names are finalized with the production owner; a dedicated `stream_got` module
must avoid cyclic layout/payload resolution.

## Frozen semantic contract

Let B be the synthetic GOT base, Q the canonical slot address, S the resolved
symbol address, A the relocation addend, and P the relocation-field address.

| Types | Result | Field |
|---|---|---|
| 9, 41, 42, 43 | Q + A - P | checked signed 32 |
| 28 | Q + A - P | 64 |
| 3 | Q - B + A | existing checked GOT32 contract |
| 27, 30 | Q - B + A | 64 |
| 26 | B + A - P | checked signed 32 |
| 29 | B + A - P | 64 |
| 25 | S + A - B | 64 |
| 31 | S + A - B for resolved static target | 64 |

Types 41/42/43 are emitted without instruction relaxation. A slot contains S,
not S+A. Addends do not distinguish slots. Undefined weak symbols retain zero
value; real undefined strong symbols fail. TLS and IFUNC do not acquire ordinary
address slots. No imported or runtime-resolved function is silently treated as
a statically known PLTOFF target.

Global identity is exact symbol name, resolved through the winning definition.
Local identity is `(object owner, symbol table, symbol ordinal)`; equal spelling
in two objects must not alias. Keep identity domains explicit rather than a
string encoding vulnerable to names impersonating another domain.

Enumerate only relocations whose target sections are allocated and emitted.
First occurrence in deterministic object/table/record order owns a slot. Find
prior occurrences by bounded-state rescanning, charging each record/read and
checking cancellation. Do not allocate a resident symbol-to-slot dictionary.

Preserve regular/COMMON addresses. B is the aligned-8 end after COMMON storage;
reserve checked 8-byte slots in the RW tail. Base-only references still receive
a stable B with zero slots. Satisfy synthetic `_GLOBAL_OFFSET_TABLE_` undefined
references before ordinary unresolved-symbol rejection/archive demand; do not
pretend an assembler-created undefined entry requires an archive provider.
Definition conflicts and local spelling must follow the explicit synthetic-symbol
policy, not silently override unrelated local definitions.

Compute regular and COMMON extent before GOT extent. Slot counting needs only
symbol identity; it must not resolve payload addresses. Payload emission may
resolve ordinary/COMMON symbols using that established layout. This prevents
GOT-base -> payload -> GOT-layout recursion. Emit actual slot bytes through
existing small windows; zero-fill only the preceding padding/COMMON portion.

All new scans share the existing work quota and cancellation owner. Validate
RELA shape, symbol references, patch widths, and checked layout growth before
publication. Output/scratch failures preserve the destination and close owners.
Logical byte/work limits are not allocator, RSS, no-GC, or whole-job enforcement;
production UnsupportedBudget remains until the complete enforcing path exists.

## Primary ABI evidence

The [AMD64 psABI Table 4.9](https://raw.githubusercontent.com/wiki/hjl-tools/x86-psabi/x86-64-psABI-1.0.pdf)
defines slot-relative, base-relative and PLTOFF formulas. Its
[optimization chapter](https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/3177443c4f5862d48f371d91ab36209f73cfe69c/x86-64-ABI/linker-optimization.tex)
describes optional GOTPCRELX transformations, including addend restrictions for
relaxation. Leaving instructions unrelaxed preserves their ordinary GOT meaning.
[LLVM extensions](https://llvm.org/docs/Extensions.html) document
`@GOTPCREL_NORELAX` as an assembler way to request type 9.

[LLVM's PLTOFF64 implementation review](https://reviews.llvm.org/D112386)
distinguishes PLT needs from symbol creation. Historical GNU gold source also
conditions PLT creation on an unresolved final value; the local experiment below
checks current GNU BFD behavior instead of treating historical code as execution.
[Binutils APX changes](https://sourceware.org/pipermail/binutils/2025-January/138632.html)
document CODE_4 GOTPCRELX handling for REX2 and MOVRS. Fixtures must use an actual
assembler or independently verified instruction encoding; a relocation number
alone does not establish an executable APX instruction. Sources accessed 2026-10-04.

## External experiment (executed, not Simple verification)

Task-owned `build/got-oracle` contains GNU as/ld probes. On Ubuntu GNU binutils
2.46, assemble `movabs $foo@PLTOFF,%rax`, `movabs $foo@GOTPLT,%rbx`, and a GOT-base
LEA; link with `ld --no-relax -static -e _start`; inspect readelf/objdump output.
The real FUNC symbol is 0x40101c, GOT base 0x402fe8, and its slot 0x402fe0.
PLTOFF64 contains -0x1fcc = S-B. GOTPLT64 contains -8 = Q-B, and the slot contains
0x40101c. There is no generated PLT instruction body. This confirms direct static
function payloads for types 30/31. Stream layout need not reproduce GNU's negative
slot offset: its synthetic base may equal the first slot.

A second object containing only PLTOFF64 (no explicit GOT-base operand) still
has a GNU-as-created GLOBAL UND NOTYPE `_GLOBAL_OFFSET_TABLE_`. GNU ld resolves
the link without slots; its displacement implies base 0x402000, and it need not
emit that symbol. The stream must likewise handle base-only demand. These probes
were not executed as programs and provide no Simple link/runtime PASS.

GNU as also assembled `movq foo@GOTPCREL(%rip),%r16` into
`d5 48 8b 05 00 00 00 00`, with CODE_4_GOTPCRELX at offset 4 and addend -4;
objdump independently decoded the APX instruction. This supplies a real type-43
fixture encoding without requiring APX execution on the host.

## Positive and negative acceptance

1. Assemble actual 9/41/42 instruction references and all remaining ordinary
   forms. Check input relocation tags and setup bounds before mutation.
2. Decode each output displacement/offset and translate addresses through real
   PT_LOAD headers. Verify Q contains S and S identifies the expected data or
   function bytes. Preserve original opcodes for unrelaxed forms, including 43.
3. Repeated global references and different addends use one slot. Same-name local
   symbols in different objects use distinct slots and correct payloads.
4. Cover COMMON target, selected archive target, undefined weak zero, and genuine
   undefined failure. Check base-only input with synthetic undefined GOT symbol
   and zero slots; check types 30/31 against resolved function bytes.
5. Ignore nonallocated relocation tables for GOT allocation. Verify deterministic
   canonical order and exact slot extent, rather than merely nonempty output.
6. Compare semantic targets with the fast linker, which may relax instructions.
   Compare stream images across narrow windows that split slots and patches.
7. Open real retained inputs before direct GOT-scan quota/cancellation checks.
   Exercise an output limit one byte below required GOT end, preserve destination
   sentinel, and assert cleanup. Test malformed symbols, patch bounds, addend or
   displacement range rejection, and unsupported TLS/IFUNC explicitly.

Specs must precede source changes, use canonical `std.spec.step`, independent
expected values, and explicit guard returns after nonfatal setup assertions.
All Simple execution, canonical manual generation, coverage, full compiler and
application links, and performance/RSS gates remain UNRUN. This document does
not mark the whole bounded engine or item 4 complete.

## Refinement: inactive and zero-slot GOT

The internal GOT layout has an explicit `active` state. An allocated ordinary
GOT relocation, or an allocated scalar relocation to the synthetic GOT anchor,
activates it. A mere unused undefined `_GLOBAL_OFFSET_TABLE_` declaration does
not activate it. This preserves existing image bytes and length for inputs that
do not demand GOT semantics.

Let `start` be the end of regular and COMMON storage. The prospective base is
`align8(start)`. An inactive layout ends at `start` and neither emits nor charges
alignment padding; unused alignment must not cause an output-budget failure.
An active zero-slot layout ends at the aligned base. Its synthetic anchor may
legally be one past the emitted extent; do not invent a reserved GOT entry.
An active layout with slots extends from that base by checked multiples of eight.

Acceptance must distinguish no GOT demand, unused synthetic declaration,
base-only demand, and scalar synthetic-anchor demand, and verify exact output
extent as well as address formulas. First executable test intent is
`15fc30e3ec3`; implementation and execution status remain separately recorded.
