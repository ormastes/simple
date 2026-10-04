# RV64 static initial-exec TLS integration

Base: `75076715f57`. Status: test-first design; runtime UNRUN.
Research: `doc/01_research/compiler/linker/riscv_static_ie_2026-10-04.md`.

## Interface and ownership

Preserve `elf_link`, `elf_link_configured`, `ElfLinkRequest`, and all existing
public relocation APIs. Private new helpers use `item4_riscv_ie_`. Runtime lane
owns `elf/reloc_scan.spl`, `elf/riscv_link_support.spl`, and
`elf/elf_static_link.spl`; acceptance lane owns fixtures, executable SSpec and
manual; research lane owns this design and its research companion. Root owns
integration and the common ledger. No sidecars are needed.

## Production flow

1. Classify RV64 TLS_GOT_HI20 as IE, validate the defined TLS target and zero
   addend, and retain existing unsupported-mode checks.
2. Allocate a GOT word with IE payload semantics. Do not let a symbol-key
   collision substitute an ordinary address word for a TP-offset word.
   Repeated equivalent IE references may reuse a slot.
3. Add type 21 to the checked high-relocation index. Resolve its paired low
   relocation through the actual high-site identity; preserve duplicate,
   missing-pair, instruction and range checks.
4. Patch AUIPC/LD using the slot's address relative to the high instruction.
   The low relocation must inherit that displacement, not use the TLS symbol
   or its own instruction address as the origin.
5. Fill the word with the statically resolved TP-relative offset. Preserve the
   real PT_TLS and STT_TLS metadata, initialized image and zero-fill extent.

The existing static driver remains the caller. This change must not reroute
through an external linker or claim a loader performed unresolved work.

## Tests before implementation

The positive fixture must include nonzero initialized TLS and aligned zero-fill
TLS, repeated IE loads and an ordinary GOT address. Use independent expected
offsets, checked section/program-header ranges, and AUIPC/LD field decoding.
Verify all setup relocation types before mutating a negative fixture. Assert
zero-addend, TLS-kind and pair failures through `elf_link`, not a helper alone.
Matchers do not abort: failed setup or bounds assertions need explicit returns.

Fixture assembly or an LLD oracle is evidence about the fixture/toolchain, not
a Simple runtime PASS. The Simple specs and canonical manual generation remain
UNRUN until a runtime is independently admitted. No runtime rebuild retry is
part of this lane.

## Separate composition continuation

At this base no compiler linker calls `mdsocpp_seal_v1`; only the generic IDE
pilot calls it. The generic sealer binds descriptor facet IDs and copies its
policy digest, not executable linker callbacks or artifact trust. A future
static composition must route actual operations through typed bindings consumed
by the driver; sealing decorative descriptors does not close that gate.
Byte-source binding belongs at a real input-read boundary, not a parser renamed
as I/O. This audit is retained for the next composition wave and adds no scope
to this TLS change. CLI, trusted manifest, full compositions and bounded-memory
enforcement remain separate open requirements.
